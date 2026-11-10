module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineSourceComparison
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.CechMultifork
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelSystemGlue
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartAdjunct
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleChartComparison

/-!
# The kernel of a functor on quasi-coherent modules, and the comparison transformation

Let `R` be a ring, `X` and `Y` schemes over `R` with `X` quasi-compact with affine diagonal, and
`F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` an `R`-linear, right exact functor commuting with arbitrary direct
sums.  This file proves [Stacks, Tag 0GPA]: there are a quasi-coherent module `K` on `X ×_R Y`
and a natural transformation `t : F ⟶ F_K` such that `t ∘ f_* : F ∘ f_* ⟶ F_K ∘ f_*` is an
isomorphism for every morphism `f : X' ⟶ X` whose source is affine.

The construction of `K` and `t` only ever evaluates `F` on direct images from affine opens, so
it is carried out under the weaker hypothesis
`AlgebraicGeometry.affineOpenRightExactLinearCoproductFunctor` (`F` is `R`-linear, commutes with
arbitrary direct sums, and is right exact after direct image along every open immersion with
affine source); this is what Tag 0GPB needs.  Right exactness of `F` itself is used only in the
final assertion about arbitrary morphisms with affine source.

The kernel `K` is `AlgebraicGeometry.AffineChartKernels.glued` of
`AlgebraicGeometry.openKernelSystem`: the kernels of `F ∘ j_{U,*}` on `U ×_R Y`, for the affine
opens `U` of `X`, glued along the identifications of Tag 0FZF.  The restriction of `K` to the
chart of `U` is the kernel of `U` (`AlgebraicGeometry.AffineChartKernels.chartKernelIso`), and the
identifications through two affine opens agree on their intersection
(`AlgebraicGeometry.AffineChartKernels.chartKernelRestrictIso_inf`).

On direct images from an affine open `U` the functors `F` and `F_K` are compared through the
kernel of `U` (`AlgebraicGeometry.openComparison`), and these comparisons are compatible with the
restriction maps of the Čech multifork (`AlgebraicGeometry.openComparison_cechRestr`).  Since
`F_K` carries the Čech multifork of the cover of `X` by its affine opens to a limit
(`AlgebraicGeometry.isLimitIntegralTransformCechMultifork`), the legs
`F(G) ⟶ F((U ↪ X)_*(G|_U)) ≅ F_K((U ↪ X)_*(G|_U))` lift to a map `t_G : F(G) ⟶ F_K(G)`, natural
in `G` (`AlgebraicGeometry.kernelTransform`).

At a direct image `(U ↪ X)_* N` the unit of restriction is an isomorphism, so `t` is an
isomorphism there (`AlgebraicGeometry.isIso_kernelTransform_app_pushforward`).  For `f : X' ⟶ X`
with `X'` affine, both `F ∘ f_*` and `F_K ∘ f_*` are integral transforms on `X'`
(`AlgebraicGeometry.affineSourceKernelIso` and
`AlgebraicGeometry.quasicoherentIntegralTransformSourceChangeIso'`), so both carry the Čech
multifork of the cover of `X'` by the inverse images of the affine opens of `X` to a limit; on the
terms of that multifork `t ∘ f_*` is evaluated at direct images from affine opens of `X`, hence is
an isomorphism, and so it is an isomorphism at the cone point
(`AlgebraicGeometry.isIso_whiskerLeft_kernelTransform`).

## Main definitions

* `AlgebraicGeometry.openKernelSystem`: the compatible system of the kernels of the affine opens.
* `AlgebraicGeometry.kernelTransform`: **the natural transformation `t : F ⟶ F_K`** for the glued
  kernel.

## Main results

* `AlgebraicGeometry.isIso_whiskerLeft_kernelTransform`: `t ∘ f_*` is an isomorphism for every
  morphism `f : X' ⟶ X` over `R` with `X'` affine.
* `AlgebraicGeometry.exists_kernel_natTrans_isIso_whiskerLeft_pushforward`: **Tag 0GPA.**

## References

* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace RestrictIsoGlueData

variable {S : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}} {f : ∀ i, Z i ⟶ S}
  [∀ i, IsOpenImmersion (f i)] (D : RestrictIsoGlueData S f)

/-- **The chart comparisons of the glued module are compatible with the comparison data**, as
morphisms of sheaves of modules:  over an open `V` inside two chart ranges, the restriction to
`V` of the `i`-th transposed chart comparison, followed by the comparison from `i` to `j`, is the
restriction to `V` of the `j`-th transposed chart comparison. -/
theorem restrictFunctor_map_chartAdjunct_comp_iso_of_le_opensRange (i j : ι) {V : S.Opens}
    (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange) :
    (Scheme.Modules.restrictFunctor V.ι).map (D.toModulesGlueData.chartAdjunct i) ≫
        (D.iso i j hi hj).hom =
      (Scheme.Modules.restrictFunctor V.ι).map (D.toModulesGlueData.chartAdjunct j) :=
  restrictFunctor_map_comp_eq _ _ _ fun _V' hV' => app_comp_localApp hV' _ _ _ fun s =>
    (D.trans_eq_localAppFun_le i j hi hj hV' _).symm.trans
      (D.toModulesGlueData.trans_chartAdjunct i j _ _ s)

end RestrictIsoGlueData

/-! ### Restricting a chart identification along the factorisation of an open -/

section ChartRestrict

variable {S A T : Scheme.{u}} (a : A ⟶ S) (t : T ⟶ S) (p : T ⟶ A) (hp : p ≫ a = t)
  [IsOpenImmersion a] [IsOpenImmersion t] [IsOpenImmersion p]

/-- **The restriction of a chart identification to an open, through the factorisation of the
open.**  Let `φ : G ⟶ a_* M` transpose an identification `χ` of the restriction of `G` along `a`
with `M`, let `σ` identify the restriction of `M` along `p` with `L`, and let `V` be an open inside
the range of `t = p ≫ a`.  Restricting the identification `G|_t ≅ L` along the factorisation of
`V` through `t` is, up to the comparison of iterated restrictions, the restriction of `φ` to `V`
followed by the chart comparison at `V` and by `σ`. -/
theorem restrictCompIso_hom_map_restrictChartIso {G : S.Modules} {M : A.Modules} {L : T.Modules}
    (φ : G ⟶ (Scheme.Modules.pushforward a).obj M) (χ : Scheme.Modules.restrict G a ≅ M)
    (hχ : (Scheme.Modules.restrictFunctor a).map φ ≫
        ((Scheme.Modules.restrictFunctorAdjCounitIso a).app M).hom = χ.hom)
    (σ : Scheme.Modules.restrict M p ≅ L) {V : S.Opens} (hV : V ≤ t.opensRange) :
    (restrictCompIso (openLift t hV) t (openLift_comp t hV) G).hom ≫
        (Scheme.Modules.restrictFunctor (openLift t hV)).map
          (restrictChartIso a χ p hp ≪≫ σ).hom =
      (Scheme.Modules.restrictFunctor V.ι).map φ ≫
        (openLiftRestrictIso a M (hV.trans (opensRange_le_of_comp a hp))).hom ≫
          (restrictChartIso p σ (openLift t hV) (openLift_comp_eq a hp hV)).hom := by
  simp only [restrictChartIso, openLiftRestrictIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc (restrictCompIso (openLift t hV) t (openLift_comp t hV) G).hom,
    restrictCompIso_assoc (openLift t hV) p a hp (openLift_comp t hV)
      (openLift_comp_eq a hp hV) G, Category.assoc,
    ← Category.assoc (restrictCompIso (openLift t hV) p (openLift_comp_eq a hp hV)
      (Scheme.Modules.restrict G a)).hom,
    ← restrictCompIso_naturality (openLift t hV) p (openLift_comp_eq a hp hV) χ.hom,
    ← Category.assoc ((Scheme.Modules.restrictFunctor V.ι).map φ),
    restrictCompIso_naturality (openLift a (hV.trans (opensRange_le_of_comp a hp))) a
      (openLift_comp a _) φ, ← hχ]
  simp only [Functor.map_comp, Category.assoc]

end ChartRestrict

/-- Restriction along an isomorphism that is an open immersion is faithful. -/
theorem restrictFunctor_map_injective_of_isIso {A B : Scheme.{u}} (e : A ⟶ B)
    [IsOpenImmersion e] [IsIso e] {M N : B.Modules} {x y : M ⟶ N}
    (h : (Scheme.Modules.restrictFunctor e).map x = (Scheme.Modules.restrictFunctor e).map y) :
    x = y := by
  let α : 𝟭 B.Modules ≅ Scheme.Modules.restrictFunctor e ⋙
      Scheme.Modules.restrictFunctor (inv e) :=
    Scheme.Modules.restrictFunctorId.symm ≪≫
      Scheme.Modules.restrictFunctorCongr (IsIso.inv_hom_id e).symm ≪≫
        Scheme.Modules.restrictFunctorComp (inv e) e
  have hx := α.hom.naturality x
  have hy := α.hom.naturality y
  simp only [Functor.id_map, Functor.comp_map] at hx hy
  refine (Iso.cancel_iso_hom_right x y (α.app N)).1 ?_
  rw [Iso.app_hom, hx, hy, h]

/-- An isomorphism in a full subcategory, read on the underlying objects, typed by the
`ObjectProperty.FullSubcategory.obj` projection. -/
def objIso {C : Type*} [Category C] {P : ObjectProperty C} {A B : P.FullSubcategory}
    (e : A ≅ B) : A.obj ≅ B.obj :=
  (ObjectProperty.ι P).mapIso e

/-- The forward map of `objIso e` is the underlying morphism of `e.hom`. -/
@[simp] theorem objIso_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {A B : P.FullSubcategory} (e : A ≅ B) : (objIso e).hom = e.hom.hom := rfl

/-! ### Identifications of inverse images, read on restrictions -/

section Bridge

variable (R : Type u) [CommRing R] (Y : Over (Spec (.of R)))

/-- **A cocycle of identifications of inverse images of quasi-coherent kernels, read on
restrictions.**  This is `AlgebraicGeometry.restrictChartIso_pullback_trans` fed with
`AlgebraicGeometry.pullbackCompIsoOfEq_sourceChangeKernel`, stated with every kernel a variable so
that the instance at concrete kernels only instantiates it. -/
theorem restrictChartIso_sourceChangeKernel_trans {W V V' : Over (Spec (.of R))} (j : V ⟶ W)
    (j' : V' ⟶ V) {m : V' ⟶ W} (hm : j' ≫ j = m)
    [IsOpenImmersion (sourceChangeMap R W V Y j)] [IsOpenImmersion (sourceChangeMap R V V' Y j')]
    [IsOpenImmersion (sourceChangeMap R W V' Y m)]
    {K : Scheme.QuasicoherentModules (pullback W.hom Y.hom)}
    {L : Scheme.QuasicoherentModules (pullback V.hom Y.hom)}
    {N : Scheme.QuasicoherentModules (pullback V'.hom Y.hom)}
    (ρ : sourceChangeKernel R W V Y j K ≅ L) (ρ' : sourceChangeKernel R V V' Y j' L ≅ N)
    (ρ'' : sourceChangeKernel R W V' Y m K ≅ N)
    (hk : sourceChangeMap R V V' Y j' ≫ sourceChangeMap R W V Y j = sourceChangeMap R W V' Y m)
    (hc : eqToHom (congrArg (fun q : V' ⟶ W ↦ sourceChangeKernel R W V' Y q K) hm.symm) ≫
        (sourceChangeKernelCompIso R W V V' Y j j' K).hom ≫
          sourceChangeKernelMap R V V' Y j' ρ.hom ≫ ρ'.hom = ρ''.hom) :
    restrictChartIso (sourceChangeMap R W V Y j)
        ((Scheme.Modules.restrictFunctorIsoPullback (sourceChangeMap R W V Y j)).app K.obj ≪≫
          objIso ρ) (sourceChangeMap R V V' Y j') hk ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback (sourceChangeMap R V V' Y j')).app L.obj ≪≫
          objIso ρ') =
      (Scheme.Modules.restrictFunctorIsoPullback (sourceChangeMap R W V' Y m)).app K.obj ≪≫
        objIso ρ'' :=
  restrictChartIso_pullback_trans _ _ hk (objIso ρ) (objIso ρ') (objIso ρ'')
    (pullbackCompIsoOfEq_sourceChangeKernel R Y j j' hm ρ ρ' ρ'' (objIso ρ) (objIso ρ')
      (objIso ρ'') rfl rfl rfl hk hc)

end Bridge

/-! ### The chart identifications of the glued kernel agree on the overlaps -/

namespace AffineChartKernels

variable {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))} (S : AffineChartKernels R X Y)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

/-- The module of the glue data at the chart of `U` is the kernel of `U`. -/
theorem glueData_mod {U : X.left.Opens} (hU : IsAffineOpen U) :
    S.glueData.mod ⟨U, hU⟩ = (S.kern hU).obj := rfl

/-- The comparison of the glue data between the charts of `U` and `V`. -/
theorem glueData_iso {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {Z : (pullback X.hom Y.hom).Opens}
    (hZU : Z ≤ (baseChangeOpenTargetMap R X Y U).opensRange)
    (hZV : Z ≤ (baseChangeOpenTargetMap R X Y V).opensRange) :
    S.glueData.iso ⟨U, hU⟩ ⟨V, hV⟩ hZU hZV = S.chartIsoOver hU hV hZU hZV := rfl

/-- **The identification of the restriction of the glued module along the chart of `T ≤ U` with
the kernel of `T`, read through the chart of `U`.** -/
def chartRestrictIso {U T : X.left.Opens} (hU : IsAffineOpen U) (hT : IsAffineOpen T)
    (h : T ≤ U) :
    Scheme.Modules.restrict S.glueData.toModulesGlueData.glued
        (baseChangeOpenTargetMap R X Y T) ≅ (S.kern hT).obj :=
  restrictChartIso (baseChangeOpenTargetMap R X Y U) (S.glueData.chartIso ⟨U, hU⟩)
    (openSubChartMap R X Y h) (openSubChartMap_comp R X Y h) ≪≫ S.sigma hU hT h

/-- **The two identifications of the restriction of the glued module along the chart of `U ∩ V`
with the kernel of `U ∩ V`, through the chart of `U` and through the chart of `V`, agree.** -/
theorem chartRestrictIso_inf {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    S.chartRestrictIso hU (hU.inf hV) inf_le_left =
      S.chartRestrictIso hV (hU.inf hV) inf_le_right := by
  have hZ0 := (opensRange_baseChangeOpenTargetMap_inf R X Y U V).symm.le
  have hZU := hZ0.trans inf_le_left
  have hZV := hZ0.trans inf_le_right
  have h1 := S.glueData.restrictFunctor_map_chartAdjunct_comp_iso_of_le_opensRange ⟨U, hU⟩ ⟨V, hV⟩
    hZU hZV
  have hZ := (opensRange_baseChangeOpenTargetMap_inf R X Y U V).le.trans' (le_inf hZU hZV)
  have key := fun {W : X.left.Opens} (hW : IsAffineOpen W) (h : U ⊓ V ≤ W) =>
    restrictCompIso_hom_map_restrictChartIso (baseChangeOpenTargetMap R X Y W)
      (baseChangeOpenTargetMap R X Y (U ⊓ V)) (openSubChartMap R X Y h)
      (openSubChartMap_comp R X Y h) (S.glueData.toModulesGlueData.chartAdjunct ⟨W, hW⟩)
      (S.glueData.chartIso ⟨W, hW⟩)
      (S.glueData.toModulesGlueData.restrictFunctor_map_chartAdjunct ⟨W, hW⟩)
      (S.sigma hW (hU.inf hV) h) hZ
  have hU' := key hU inf_le_left
  have hV' := key hV inf_le_right
  have hiso : IsIso (openLift (baseChangeOpenTargetMap R X Y (U ⊓ V)) hZ) := by
    rw [← eq_openLift _ hZ _ (Scheme.Hom.isoOpensRange_inv_comp _)]
    infer_instance
  refine Iso.ext (restrictFunctor_map_injective_of_isIso
    (openLift (baseChangeOpenTargetMap R X Y (U ⊓ V)) hZ) ?_)
  rw [← cancel_epi (restrictCompIso (openLift (baseChangeOpenTargetMap R X Y (U ⊓ V)) hZ)
    (baseChangeOpenTargetMap R X Y (U ⊓ V)) (openLift_comp _ hZ)
    S.glueData.toModulesGlueData.glued).hom]
  simp only [chartRestrictIso]
  refine hU'.trans ?_
  refine Eq.trans ?_ hV'.symm
  rw [glueData_iso] at h1
  dsimp only [RestrictIsoGlueData.toModulesGlueData_mod, glueData_mod] at h1 ⊢
  rw [← h1]
  simp only [chartIsoOver, restrictPushforwardIsoOfRestrictIso, middleIso,
    restrictMiddleIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- **The restriction of the glued kernel to the chart of an affine open `U` is the kernel of
`U`**, read as an identification of the inverse image `(U ×_R Y ⟶ X ×_R Y)^*K`. -/
def chartKernelIso {U : X.left.Opens} (hU : IsAffineOpen U) :
    sourceChangeKernel R X (openSubOver R X U) Y (openSubOverHom R X U) S.glued ≅ S.kern hU :=
  ObjectProperty.isoMk _
    (((Scheme.Modules.restrictFunctorIsoPullback (baseChangeOpenTargetMap R X Y U)).app
      S.glueData.toModulesGlueData.glued).symm ≪≫ S.glueData.chartIso ⟨U, hU⟩)

/-- **The identification of the restriction of the glued kernel to the chart of `T ≤ U` with
the kernel of `T`, through the chart of `U`**:  the identification for `U`, carried to `T` by
Tag 0FZF. -/
def chartKernelRestrictIso {U T : X.left.Opens} (hU : IsAffineOpen U) (hT : IsAffineOpen T)
    (h : T ≤ U) :
    sourceChangeKernel R X (openSubOver R X T) Y (openSubOverHom R X T) S.glued ≅ S.kern hT :=
  eqToIso (congrArg (fun q : openSubOver R X T ⟶ X ↦
      sourceChangeKernel R X (openSubOver R X T) Y q S.glued)
      (openSubInclusionOver_comp R X h).symm) ≪≫
    sourceChangeKernelCompIso R X (openSubOver R X U) (openSubOver R X T) Y
      (openSubOverHom R X U) (openSubInclusionOver R X h) S.glued ≪≫
    (sourceChangeKernelFunctor R (openSubOver R X U) (openSubOver R X T) Y
      (openSubInclusionOver R X h)).mapIso (S.chartKernelIso hU) ≪≫
    S.restrictIso hU hT h

/-- The underlying morphism of `AlgebraicGeometry.AffineChartKernels.chartKernelRestrictIso`. -/
theorem chartKernelRestrictIso_hom {U T : X.left.Opens} (hU : IsAffineOpen U)
    (hT : IsAffineOpen T) (h : T ≤ U) :
    (S.chartKernelRestrictIso hU hT h).hom =
      eqToHom (congrArg (fun q : openSubOver R X T ⟶ X ↦
          sourceChangeKernel R X (openSubOver R X T) Y q S.glued)
          (openSubInclusionOver_comp R X h).symm) ≫
        (sourceChangeKernelCompIso R X (openSubOver R X U) (openSubOver R X T) Y
          (openSubOverHom R X U) (openSubInclusionOver R X h) S.glued).hom ≫
        sourceChangeKernelMap R (openSubOver R X U) (openSubOver R X T) Y
          (openSubInclusionOver R X h) (S.chartKernelIso hU).hom ≫
        (S.restrictIso hU hT h).hom := rfl

omit [IsAffineHom (pullback.diagonal (terminal.from X.left))] in
/-- The chart maps of the opens of `X` compose, spelled with
`AlgebraicGeometry.sourceChangeMap`. -/
theorem sourceChangeMap_openSubInclusionOver_comp {U T : X.left.Opens} (h : T ≤ U) :
    sourceChangeMap R (openSubOver R X U) (openSubOver R X T) Y (openSubInclusionOver R X h) ≫
        sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U) =
      sourceChangeMap R X (openSubOver R X T) Y (openSubOverHom R X T) :=
  openSubChartMap_comp R X Y h

/-- **The identification through the chart of `U`, read on restrictions, is
`AlgebraicGeometry.AffineChartKernels.chartRestrictIso`.** -/
theorem chartKernelRestrictIso_eq {U T : X.left.Opens} (hU : IsAffineOpen U)
    (hT : IsAffineOpen T) (h : T ≤ U) :
    (Scheme.Modules.restrictFunctorIsoPullback (baseChangeOpenTargetMap R X Y T)).app
          S.glueData.toModulesGlueData.glued ≪≫
        objIso (S.chartKernelRestrictIso hU hT h) =
      S.chartRestrictIso hU hT h := by
  have key := restrictChartIso_sourceChangeKernel_trans R Y (openSubOverHom R X U)
    (openSubInclusionOver R X h) (openSubInclusionOver_comp R X h) (S.chartKernelIso hU)
    (S.restrictIso hU hT h) (S.chartKernelRestrictIso hU hT h)
    (sourceChangeMap_openSubInclusionOver_comp h) (S.chartKernelRestrictIso_hom hU hT h).symm
  have e1 : (Scheme.Modules.restrictFunctorIsoPullback
        (sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U))).app
          S.glued.obj ≪≫ objIso (S.chartKernelIso hU) =
      S.glueData.chartIso ⟨U, hU⟩ :=
    Iso.ext (Iso.hom_inv_id_assoc ((Scheme.Modules.restrictFunctorIsoPullback
      (sourceChangeMap R X (openSubOver R X U) Y (openSubOverHom R X U))).app
        S.glued.obj) (S.glueData.chartIso ⟨U, hU⟩).hom)
  rw [e1] at key
  exact key.symm

/-- **The two identifications of the inverse image of the glued kernel to the chart of `U ∩ V`
with the kernel of `U ∩ V`, through the chart of `U` and through the chart of `V`, agree.** -/
theorem chartKernelRestrictIso_inf {U V : X.left.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) :
    S.chartKernelRestrictIso hU (hU.inf hV) inf_le_left =
      S.chartKernelRestrictIso hV (hU.inf hV) inf_le_right := by
  have h := congrArg Iso.hom ((S.chartKernelRestrictIso_eq hU (hU.inf hV) inf_le_left).trans
    ((S.chartRestrictIso_inf hU hV).trans
      (S.chartKernelRestrictIso_eq hV (hU.inf hV) inf_le_right).symm))
  exact Iso.ext ((ObjectProperty.ι _).map_injective ((Iso.cancel_iso_hom_left _ _ _).1 h))

end AffineChartKernels


section PushforwardEq

private lemma presheafMapEq2 {Z : Scheme.{u}} (M : Z.Modules) {P Q : (Z.Opens)ᵒᵖ}
    (h h' : P ⟶ Q) : M.presheaf.map h = M.presheaf.map h' := by
  rw [Subsingleton.elim h h']

variable {S : Scheme.{u}} {X₀ X₁ X₂ : Over S} (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁)
  [IsAffineHom f.left] [IsAffineHom g.left]

/-- The transport along `quasicoherentPushforward_eq_comp` at a composite given as such is the
identity on sections. -/
theorem eqToIso_quasicoherentPushforward_eq_comp_rfl_inv_app_app
    [IsAffineHom (g ≫ f).left] (N : Scheme.QuasicoherentModules X₂.left) (T : X₀.left.Opens) :
    Scheme.Modules.Hom.app ((eqToIso (quasicoherentPushforward_eq_comp f g rfl)).inv.app N).hom T =
      𝟙 _ := rfl

/-- **The transport along `quasicoherentPushforward_eq_comp`, on sections**, is the restriction
map of the module along the equality of the two inverse images of the open. -/
theorem eqToIso_quasicoherentPushforward_eq_comp_inv_app_app {f' : X₂ ⟶ X₀}
    (hk : g ≫ f = f')
    [IsAffineHom f'.left] (N : Scheme.QuasicoherentModules X₂.left) (T : X₀.left.Opens) :
    Scheme.Modules.Hom.app ((eqToIso (quasicoherentPushforward_eq_comp f g hk)).inv.app N).hom T =
      (Scheme.Modules.presheaf (X := X₂.left) N.obj).map (eqToHom (by subst hk; rfl :
        f'.left ⁻¹ᵁ T = g.left ⁻¹ᵁ f.left ⁻¹ᵁ T)).op := by
  subst hk
  rw [eqToIso_quasicoherentPushforward_eq_comp_rfl_inv_app_app]
  exact ((Scheme.Modules.presheaf N.obj).map_id _).symm

/-- The comparison of the composite direct image followed by the transport along an equality of
morphisms, on sections, is a restriction map. -/
theorem pushforwardComp_hom_app_comp_pushforwardCongr_hom_app_app {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) {c : A ⟶ C} (p : a ≫ b = c) (M : A.Modules) (T : C.Opens) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pushforwardComp a b).hom.app M ≫
        (Scheme.Modules.pushforwardCongr p).hom.app M) T =
      M.presheaf.map (eqToHom (by subst p; rfl : c ⁻¹ᵁ T = a ⁻¹ᵁ b ⁻¹ᵁ T)).op := by
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  exact presheafMapEq2 M _ _

/-- **The transport along `quasicoherentPushforward_eq_comp`, on the underlying modules.** -/
theorem eqToIso_quasicoherentPushforward_eq_comp_inv_app_hom {f' : X₂ ⟶ X₀}
    (hk : g ≫ f = f')
    [IsAffineHom f'.left] (N : Scheme.QuasicoherentModules X₂.left) :
    ((eqToIso (quasicoherentPushforward_eq_comp f g hk)).inv.app N).hom =
      (Scheme.Modules.pushforwardComp g.left f.left).hom.app N.obj ≫
        (Scheme.Modules.pushforwardCongr (congrArg Over.Hom.left hk)).hom.app N.obj :=
  Scheme.Modules.hom_ext _ _ fun T =>
    (eqToIso_quasicoherentPushforward_eq_comp_inv_app_app f g hk N T).trans
      (pushforwardComp_hom_app_comp_pushforwardCongr_hom_app_app g.left f.left
        (congrArg Over.Hom.left hk) N.obj T).symm

end PushforwardEq

/-! ### The restriction maps of the Čech multifork, through the open subschemes over `R` -/

section CechRestrOver

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

attribute [local instance] isAffineHom_left_of_isAffine_left

/-- Restriction to `W ≤ U` of quasi-coherent modules in two steps is restriction in one step. -/
def qcohRestrictComp {U W : X.left.Opens} (h : W ≤ U) (G : Scheme.QuasicoherentModules X.left) :
    (qcohRestrict (X.left.homOfLE h)).obj ((qcohRestrict U.ι).obj G) ≅
      (qcohRestrict W.ι).obj G :=
  ObjectProperty.isoMk _
    (restrictCompIso (X.left.homOfLE h) U.ι (Scheme.homOfLE_ι X.left h) G.obj).symm

private alias presheaf_map_eq'' := presheafMapEq2

/-- **The restriction map of the Čech multifork from `U` to `W ≤ U`**, written as the direct
image
along `U` of the unit of restriction to `W` inside `U`, the transport identifying the composite
direct image with the direct image along `W`, and the comparison of the iterated restriction. -/
theorem cechRestr_app_eq {U W : X.left.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (h : W ≤ U) (G : Scheme.QuasicoherentModules X.left) :
    letI : IsAffine (openSubOver R X U).left := hU
    letI : IsAffine (openSubOver R X W).left := hW
    letI : QuasiCompact U.ι := inferInstanceAs (QuasiCompact (openSubOverHom R X U).left)
    letI : QuasiSeparated U.ι := inferInstanceAs (QuasiSeparated (openSubOverHom R X U).left)
    letI : QuasiCompact W.ι := inferInstanceAs (QuasiCompact (openSubOverHom R X W).left)
    letI : QuasiSeparated W.ι := inferInstanceAs (QuasiSeparated (openSubOverHom R X W).left)
    letI : QuasiCompact (X.left.homOfLE h) :=
      inferInstanceAs (QuasiCompact (openSubInclusionOver R X h).left)
    letI : QuasiSeparated (X.left.homOfLE h) :=
      inferInstanceAs (QuasiSeparated (openSubInclusionOver R X h).left)
    (cechRestr (X := X.left) (V := U) (W := W) h).app G =
      (quasicoherentPushforward (openSubOverHom R X U).left).map
          ((qcohRestrictAdjunction (X.left.homOfLE h)).unit.app ((qcohRestrict U.ι).obj G)) ≫
        (eqToIso (quasicoherentPushforward_eq_comp (openSubOverHom R X U)
          (openSubInclusionOver R X h) (openSubInclusionOver_comp R X h))).inv.app
            ((qcohRestrict (X.left.homOfLE h)).obj ((qcohRestrict U.ι).obj G)) ≫
        (quasicoherentPushforward (openSubOverHom R X W).left).map
          (qcohRestrictComp R X h G).hom := by
  let : IsAffine (openSubOver R X U).left := hU
  let : IsAffine (openSubOver R X W).left := hW
  let : QuasiCompact (X.left.homOfLE h) :=
    inferInstanceAs (QuasiCompact (openSubInclusionOver R X h).left)
  let : QuasiSeparated (X.left.homOfLE h) :=
    inferInstanceAs (QuasiSeparated (openSubInclusionOver R X h).left)
  refine (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι.map_injective ?_
  have hb := eqToIso_quasicoherentPushforward_eq_comp_inv_app_hom (openSubOverHom R X U)
    (openSubInclusionOver R X h) (openSubInclusionOver_comp R X h)
    ((qcohRestrict (X.left.homOfLE h)).obj ((qcohRestrict U.ι).obj G))
  have ha := qcohRestrictAdjunction_unit_app_hom (X.left.homOfLE h) ((qcohRestrict U.ι).obj G)
  refine Eq.trans ?_ ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι.map_comp _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·)
    ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι.map_comp _ _).symm)
  change restrictPushModMap h G.obj =
    (Scheme.Modules.pushforward U.ι).map
        ((qcohRestrictAdjunction (X.left.homOfLE h)).unit.app ((qcohRestrict U.ι).obj G)).hom ≫
      ((eqToIso (quasicoherentPushforward_eq_comp (openSubOverHom R X U)
          (openSubInclusionOver R X h) (openSubInclusionOver_comp R X h))).inv.app
            ((qcohRestrict (X.left.homOfLE h)).obj ((qcohRestrict U.ι).obj G))).hom ≫
      (Scheme.Modules.pushforward W.ι).map (qcohRestrictComp R X h G).hom.hom
  rw [ha, hb]
  rfl

end CechRestrOver



/-- **The diagram chase behind `AlgebraicGeometry.openComparison_cechRestr`**, with every object
and morphism a variable. -/
theorem cechRestr_comparison_chase {C D : Type*} [Category C] [Category D] (P Q : C ⥤ D)
    {x0 x1 x2 x3 : C} (r : x0 ⟶ x3) (A : x0 ⟶ x1) (B : x1 ⟶ x2) (C' : x2 ⟶ x3)
    (hr : r = A ≫ B ≫ C') (Binv : x2 ⟶ x1) (hB : B ≫ Binv = 𝟙 _)
    (ψ0 : P.obj x0 ⟶ Q.obj x0) (ψ1 : P.obj x1 ⟶ Q.obj x1) (ψ2 : P.obj x2 ⟶ Q.obj x2)
    (ψ3 : P.obj x3 ⟶ Q.obj x3) (nW : P.map C' ≫ ψ3 = ψ2 ≫ Q.map C')
    (hK : ψ2 = P.map Binv ≫ ψ1 ≫ Q.map B) (nU : P.map A ≫ ψ1 = ψ0 ≫ Q.map A) :
    P.map r ≫ ψ3 = ψ0 ≫ Q.map r := by
  subst hr
  simp only [Functor.map_comp, Category.assoc, nW, hK]
  rw [← P.map_comp_assoc, ← P.map_comp_assoc, Category.assoc, hB, Category.comp_id,
    reassoc_of% nU]

/-! ### Two facts about natural transformations -/

/-- A natural transformation that is an isomorphism at an object is one at every isomorphic
object. -/
theorem isIso_app_of_iso_of_isIso_app {C D : Type*} [Category C] [Category D] {P Q : C ⥤ D}
    (τ : P ⟶ Q) {A B : C} (e : A ≅ B) (hB : IsIso (τ.app B)) : IsIso (τ.app A) := by
  have h : P.map e.hom ≫ τ.app B ≫ Q.map e.inv = τ.app A := by
    rw [τ.naturality_assoc, ← Q.map_comp, e.hom_inv_id, Q.map_id, Category.comp_id]
  rw [← h]
  infer_instance

/-- **A natural transformation between two functors that both carry a cone to a limit, and that
is an isomorphism on the diagram, is an isomorphism at the cone point.** -/
theorem isIso_app_pt_of_isLimit {J C D : Type*} [Category J] [Category C] [Category D]
    {K : J ⥤ C} {P Q : C ⥤ D} (τ : P ⟶ Q) (c : Cone K) (hP : IsLimit (P.mapCone c))
    (hQ : IsLimit (Q.mapCone c)) (h : ∀ j, IsIso (τ.app (K.obj j))) : IsIso (τ.app c.pt) := by
  have : ∀ j, IsIso ((Functor.whiskerLeft K τ).app j) := h
  have : IsIso (Functor.whiskerLeft K τ) := NatIso.isIso_of_isIso_app _
  let hP' := (IsLimit.postcomposeHomEquiv (asIso (Functor.whiskerLeft K τ)) _).symm hP
  have e : τ.app c.pt =
      hQ.lift ((Cone.postcompose (Functor.whiskerLeft K τ)).obj (P.mapCone c)) := by
    refine hQ.hom_ext fun j => ?_
    rw [hQ.fac]
    exact (τ.naturality (c.π.app j)).symm
  rw [e]
  exact (IsLimit.conePointUniqueUpToIso hP' hQ).isIso_hom

/-- Two morphisms that agree after `x` agree after any morphism through which `x` factors. -/
theorem comp_eq_comp_of_comp_eq_comp {C : Type*} [Category C] {T A B E : C} {a b : T ⟶ A}
    {x : A ⟶ B} {y : B ⟶ E} {z : A ⟶ E} (h : a ≫ x = b ≫ x) (hw : x ≫ y = z) :
    a ≫ z = b ≫ z := by
  rw [← hw, ← Category.assoc, h, Category.assoc]

/-- **A cone over a multicospan of shape `prod ι` from legs to the left objects** that agree
on the right objects. -/
def multicospanLegsCone {C : Type*} [Category C] {ι : Type*}
    (D : WalkingMulticospan (MulticospanShape.prod ι) ⥤ C) (T : C)
    (l : ∀ i : ι, T ⟶ D.obj (.left i))
    (hl : ∀ p : ι × ι,
      l p.1 ≫ D.map (multicospanFst p) = l p.2 ≫ D.map (multicospanSnd p)) :
    Cone D where
  pt := T
  π :=
    { app := fun A => match A with
        | .left i => l i
        | .right p => l p.1 ≫ D.map (multicospanFst p)
      naturality := by
        rintro _ _ (A | b | b)
        · simp only [WalkingMulticospan.Hom.id_eq_id, Functor.const_obj_map,
            CategoryTheory.Functor.map_id, Category.comp_id]
          exact Category.id_comp _
        · exact Category.id_comp _
        · exact (Category.id_comp _).trans (hl b) }

/-- The diagram chase behind the naturality of `AlgebraicGeometry.kernelTransform`. -/
theorem kernelTransform_naturality_chase {C D : Type*} [Category C] [Category D] (P Q : C ⥤ D)
    {g g' e e' : C} (φ : g ⟶ g') (η : g ⟶ e) (η' : g' ⟶ e') (ψφ : e ⟶ e')
    (hn : φ ≫ η' = η ≫ ψφ) (ψ : P.obj e ⟶ Q.obj e) (ψ' : P.obj e' ⟶ Q.obj e')
    (hψ : P.map ψφ ≫ ψ' = ψ ≫ Q.map ψφ) (a : P.obj g ⟶ Q.obj g)
    (a' : P.obj g' ⟶ Q.obj g')
    (ha : a ≫ Q.map η = P.map η ≫ ψ) (ha' : a' ≫ Q.map η' = P.map η' ≫ ψ') :
    (P.map φ ≫ a') ≫ Q.map η' = (a ≫ Q.map φ) ≫ Q.map η' := by
  rw [Category.assoc, ha', Category.assoc, ← Q.map_comp, hn, Q.map_comp, ← Category.assoc a, ha,
    ← P.map_comp_assoc, hn, P.map_comp_assoc, hψ, Category.assoc]

/-! ### The affine opens of a scheme with affine diagonal -/

section AffineFamily

variable {S : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from S))]

/-- The inclusion of an affine open of a scheme with affine diagonal is affine. -/
theorem isAffineHom_ι_of_isAffineOpen {U : S.Opens} (hU : IsAffineOpen U) : IsAffineHom U.ι :=
  have : IsAffine U.toScheme := hU
  Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source U.ι

/-- The inclusion of a member of `S.affineOpens` is affine. -/
theorem isAffineHom_ι_affineOpens (i : S.affineOpens) : IsAffineHom (i : S.Opens).ι :=
  isAffineHom_ι_of_isAffineOpen i.2

/-- The inclusion of the intersection of two members of `S.affineOpens` is affine. -/
theorem isAffineHom_ι_affineOpens_inf (i j : S.affineOpens) :
    IsAffineHom ((i : S.Opens) ⊓ (j : S.Opens)).ι :=
  isAffineHom_ι_of_isAffineOpen (IsAffineOpen.inf i.2 j.2)

end AffineFamily

/-! ### The kernels of the affine opens, glued, and the comparisons on the affine opens -/

section Concrete

attribute [local instance] isOpenImmersion_openSubOverHom_left

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]
  (hF : affineOpenRightExactLinearCoproductFunctor R X Y F)

/-- **The compatible system of the kernels of the affine opens of `X`**:  the kernel of
`F ∘ j_{U,*}` on `U ×_R Y` for every affine open `U`, with the identifications of Tag 0FZF. -/
def openKernelSystem : AffineChartKernels R X Y where
  kern hU := openKernel R X Y F hF hU
  restrictIso hU hU' h := openKernelRestrictIso R X Y F hF hU hU' h
  restrictIso_trans hU hU' hU'' hle hle' :=
    openKernelRestrictIso_trans R X Y F hF hU hU' hU'' hle hle'

variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]

attribute [local instance] isAffineHom_left_of_isAffine_left

/-- **The comparison of `F` with the integral transform of the glued kernel on direct images from
an affine open `U`**, through an identification `β` of the restriction of the glued kernel to the
chart of `U` with the kernel of `U`. -/
def openComparison {U : X.left.Opens} (hU : IsAffineOpen U)
    (β : sourceChangeKernel R X (openSubOver R X U) Y (openSubOverHom R X U)
      (openKernelSystem R X Y F hF).glued ≅ openKernel R X Y F hF hU) :
    letI : IsAffine (openSubOver R X U).left := hU
    quasicoherentPushforward (openSubOverHom R X U).left ⋙ F ≅
      quasicoherentPushforward (openSubOverHom R X U).left ⋙
        quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued :=
  letI : IsAffine (openSubOver R X U).left := hU
  kernelComparison R X Y F (openKernelSystem R X Y F hF).glued (openSubOverHom R X U)
    (affineSourceKernelIso R X Y F hF (openSubOverHom R X U)) β

/-- **The comparisons on the affine opens are compatible with the restriction maps of the Čech
multifork**, the comparison on the smaller open being taken through the identification of the
restriction of the glued kernel coming from the larger one. -/
theorem openComparison_cechRestr {U W : X.left.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (h : W ≤ U) (G : Scheme.QuasicoherentModules X.left) :
    letI : IsAffine (openSubOver R X U).left := hU
    letI : IsAffine (openSubOver R X W).left := hW
    letI : QuasiCompact U.ι := inferInstanceAs (QuasiCompact (openSubOverHom R X U).left)
    letI : QuasiSeparated U.ι := inferInstanceAs (QuasiSeparated (openSubOverHom R X U).left)
    letI : QuasiCompact W.ι := inferInstanceAs (QuasiCompact (openSubOverHom R X W).left)
    letI : QuasiSeparated W.ι := inferInstanceAs (QuasiSeparated (openSubOverHom R X W).left)
    F.map ((cechRestr (X := X.left) (V := U) (W := W) h).app G) ≫
        (openComparison R X Y F hF hW
          ((openKernelSystem R X Y F hF).chartKernelRestrictIso hU hW h)).hom.app
          ((qcohRestrict W.ι).obj G) =
      (openComparison R X Y F hF hU ((openKernelSystem R X Y F hF).chartKernelIso hU)).hom.app
          ((qcohRestrict U.ι).obj G) ≫
        (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
          ((cechRestr (X := X.left) (V := U) (W := W) h).app G) :=
  letI : IsAffine (openSubOver R X U).left := hU
  letI : IsAffine (openSubOver R X W).left := hW
  by
    let : QuasiCompact (X.left.homOfLE h) :=
      inferInstanceAs (QuasiCompact (openSubInclusionOver R X h).left)
    let : QuasiSeparated (X.left.homOfLE h) :=
      inferInstanceAs (QuasiSeparated (openSubInclusionOver R X h).left)
    have hD := cechRestr_app_eq R X hU hW h G
    have hK := kernelComparison_comp_app' R X Y F (openKernelSystem R X Y F hF).glued
      (openSubOverHom R X U) (openSubInclusionOver R X h) (openSubInclusionOver_comp R X h)
      (affineSourceKernelIso R X Y F hF (openSubOverHom R X U))
      (affineSourceKernelIso R X Y F hF (openSubOverHom R X W))
      ((openKernelSystem R X Y F hF).restrictIso hU hW h)
      (sourceChangeIso_hom_comp_map_affineSourceKernelRestrictIso R X Y F hF
        (openSubOverHom R X U) (openSubInclusionOver R X h) (openSubInclusionOver_comp R X h))
      ((openKernelSystem R X Y F hF).chartKernelIso hU)
      ((openKernelSystem R X Y F hF).chartKernelRestrictIso hU hW h)
      ((openKernelSystem R X Y F hF).chartKernelRestrictIso_hom hU hW h)
      ((qcohRestrict (X.left.homOfLE h)).obj ((qcohRestrict U.ι).obj G))
    have hK' : (openComparison R X Y F hF hW
          ((openKernelSystem R X Y F hF).chartKernelRestrictIso hU hW h)).hom.app
            ((qcohRestrict (X.left.homOfLE h)).obj ((qcohRestrict U.ι).obj G)) =
        F.map ((eqToIso (quasicoherentPushforward_eq_comp (openSubOverHom R X U)
            (openSubInclusionOver R X h) (openSubInclusionOver_comp R X h))).hom.app
              ((qcohRestrict (X.left.homOfLE h)).obj ((qcohRestrict U.ι).obj G))) ≫
          (openComparison R X Y F hF hU ((openKernelSystem R X Y F hF).chartKernelIso hU)).hom.app
            ((quasicoherentPushforward (openSubInclusionOver R X h).left).obj
              ((qcohRestrict (X.left.homOfLE h)).obj ((qcohRestrict U.ι).obj G))) ≫
          (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
            ((eqToIso (quasicoherentPushforward_eq_comp (openSubOverHom R X U)
            (openSubInclusionOver R X h) (openSubInclusionOver_comp R X h))).inv.app
              ((qcohRestrict (X.left.homOfLE h)).obj ((qcohRestrict U.ι).obj G))) := hK
    have nW := (openComparison R X Y F hF hW
      ((openKernelSystem R X Y F hF).chartKernelRestrictIso hU hW h)).hom.naturality
        (qcohRestrictComp R X h G).hom
    have nU := (openComparison R X Y F hF hU
      ((openKernelSystem R X Y F hF).chartKernelIso hU)).hom.naturality
        ((qcohRestrictAdjunction (X.left.homOfLE h)).unit.app ((qcohRestrict U.ι).obj G))
    simp only [Functor.comp_map] at nW nU
    exact cechRestr_comparison_chase F
      (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued) _ _ _ _ hD _
      (Iso.inv_hom_id_app _ _) _ _ _ _ nW hK' nU

/-! ### The transformation `t : F ⟶ F_K` -/

attribute [local instance] isAffineHom_ι_affineOpens isAffineHom_ι_affineOpens_inf

/-- The diagram chase behind `AlgebraicGeometry.cechLeg_compat`. -/
theorem cechLeg_compat_chase {C D : Type*} [Category C] [Category D] (P Q : C ⥤ D)
    {g eU eV eW : C} (ηU : g ⟶ eU) (ηV : g ⟶ eV) (ηW : g ⟶ eW) (rU : eU ⟶ eW)
    (rV : eV ⟶ eW)
    (hU : ηU ≫ rU = ηW) (hV : ηV ≫ rV = ηW) (ψU : P.obj eU ⟶ Q.obj eU)
    (ψV : P.obj eV ⟶ Q.obj eV) (ψW : P.obj eW ⟶ Q.obj eW)
    (nU : P.map rU ≫ ψW = ψU ≫ Q.map rU) (nV : P.map rV ≫ ψW = ψV ≫ Q.map rV) :
    P.map ηU ≫ ψU ≫ Q.map rU = P.map ηV ≫ ψV ≫ Q.map rV := by
  rw [← nU, ← nV, ← P.map_comp_assoc, ← P.map_comp_assoc, hU, hV]

/-- **The legs `F(G) ⟶ F_K((U ↪ X)_*(G|_U))` agree on overlaps.** -/
theorem cechLeg_compat {U V : X.left.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (G : Scheme.QuasicoherentModules X.left) :
    letI : IsAffine (openSubOver R X U).left := hU
    letI : IsAffine (openSubOver R X V).left := hV
    letI : QuasiCompact U.ι := inferInstanceAs (QuasiCompact (openSubOverHom R X U).left)
    letI : QuasiSeparated U.ι := inferInstanceAs (QuasiSeparated (openSubOverHom R X U).left)
    letI : QuasiCompact V.ι := inferInstanceAs (QuasiCompact (openSubOverHom R X V).left)
    letI : QuasiSeparated V.ι := inferInstanceAs (QuasiSeparated (openSubOverHom R X V).left)
    letI : IsAffine (openSubOver R X (U ⊓ V)).left := hU.inf hV
    letI : QuasiCompact (U ⊓ V).ι :=
      inferInstanceAs (QuasiCompact (openSubOverHom R X (U ⊓ V)).left)
    letI : QuasiSeparated (U ⊓ V).ι :=
      inferInstanceAs (QuasiSeparated (openSubOverHom R X (U ⊓ V)).left)
    F.map ((cechUnit U).app G) ≫
        (openComparison R X Y F hF hU ((openKernelSystem R X Y F hF).chartKernelIso hU)).hom.app
          ((qcohRestrict U.ι).obj G) ≫
        (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
          ((cechRestr (V := U) (W := U ⊓ V) inf_le_left).app G) =
      F.map ((cechUnit V).app G) ≫
        (openComparison R X Y F hF hV ((openKernelSystem R X Y F hF).chartKernelIso hV)).hom.app
          ((qcohRestrict V.ι).obj G) ≫
        (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
          ((cechRestr (V := V) (W := U ⊓ V) inf_le_right).app G) := by
  let : IsAffine (openSubOver R X U).left := hU
  let : IsAffine (openSubOver R X V).left := hV
  let : IsAffine (openSubOver R X (U ⊓ V)).left := hU.inf hV
  let : QuasiCompact U.ι := inferInstanceAs (QuasiCompact (openSubOverHom R X U).left)
  let : QuasiSeparated U.ι := inferInstanceAs (QuasiSeparated (openSubOverHom R X U).left)
  let : QuasiCompact V.ι := inferInstanceAs (QuasiCompact (openSubOverHom R X V).left)
  let : QuasiSeparated V.ι := inferInstanceAs (QuasiSeparated (openSubOverHom R X V).left)
  let : QuasiCompact (U ⊓ V).ι :=
    inferInstanceAs (QuasiCompact (openSubOverHom R X (U ⊓ V)).left)
  let : QuasiSeparated (U ⊓ V).ι :=
    inferInstanceAs (QuasiSeparated (openSubOverHom R X (U ⊓ V)).left)
  have nU := openComparison_cechRestr R X Y F hF hU (hU.inf hV) inf_le_left G
  have nV := openComparison_cechRestr R X Y F hF hV (hU.inf hV) inf_le_right G
  rw [← (openKernelSystem R X Y F hF).chartKernelRestrictIso_inf hU hV] at nV
  exact cechLeg_compat_chase F
    (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued) _ _ _ _ _
    (cechUnit_comp_cechRestr (V := U) (W := U ⊓ V) inf_le_left G)
    (cechUnit_comp_cechRestr (V := V) (W := U ⊓ V) inf_le_right G) _ _ _ nU nV

/-- The leg `F(G) ⟶ F_K((U ↪ X)_*(G|_U))` at an affine open `U`. -/
abbrev cechLeg (G : Scheme.QuasicoherentModules X.left) (i : X.left.affineOpens) :
    F.obj G ⟶ ((cechIndex (Subtype.val : X.left.affineOpens → X.left.Opens) G).multicospan ⋙
        quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).obj (.left i) :=
  F.map ((cechUnit (i : X.left.Opens)).app G) ≫
    (openComparison R X Y F hF i.2 ((openKernelSystem R X Y F hF).chartKernelIso i.2)).hom.app
      ((qcohRestrict (i : X.left.Opens).ι).obj G)

/-- The legs of `AlgebraicGeometry.cechLegCone` agree on the double overlaps. -/
theorem cechLeg_fst_snd (G : Scheme.QuasicoherentModules X.left)
    (p : X.left.affineOpens × X.left.affineOpens) :
    cechLeg R X Y F hF G p.1 ≫
        ((cechIndex (Subtype.val : X.left.affineOpens → X.left.Opens) G).multicospan ⋙
          quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
            (multicospanFst p) =
      cechLeg R X Y F hF G p.2 ≫
        ((cechIndex (Subtype.val : X.left.affineOpens → X.left.Opens) G).multicospan ⋙
          quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
            (multicospanSnd p) :=
  ((Category.assoc _ _ _).trans (cechLeg_compat R X Y F hF p.1.2 p.2.2 G)).trans
    (Category.assoc _ _ _).symm

/-- **The cone `F(G) ⟶ F_K(Čech diagram of G)`** for the cover of `X` by all its affine opens. -/
def cechLegCone (G : Scheme.QuasicoherentModules X.left) :
    Cone ((cechIndex (Subtype.val : X.left.affineOpens → X.left.Opens) G).multicospan ⋙
      quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued) :=
  multicospanLegsCone _ (F.obj G) (cechLeg R X Y F hF G) (cechLeg_fst_snd R X Y F hF G)

/-- `F_K` carries the Čech multifork of the cover by all affine opens to a limit. -/
def isLimitCech (G : Scheme.QuasicoherentModules X.left) :
    IsLimit ((quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).mapCone
      (cechMultifork (Subtype.val : X.left.affineOpens → X.left.Opens) G)) :=
  isLimitIntegralTransformCechMultifork R X Y (openKernelSystem R X Y F hF).glued
    (Subtype.val : X.left.affineOpens → X.left.Opens) (iSup_affineOpens_eq_top X.left) G

/-- The component at `G` of `AlgebraicGeometry.kernelTransform`. -/
def kernelTransformApp (G : Scheme.QuasicoherentModules X.left) :
    F.obj G ⟶ (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).obj G :=
  (isLimitCech R X Y F hF G).lift (cechLegCone R X Y F hF G)

/-- **The defining property of `t`**: followed by the leg at an affine open `U`, it is
`F(G) ⟶ F((U ↪ X)_*(G|_U)) ≅ F_K((U ↪ X)_*(G|_U))`. -/
theorem kernelTransformApp_comp (G : Scheme.QuasicoherentModules X.left)
    (i : X.left.affineOpens) :
    kernelTransformApp R X Y F hF G ≫
        (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
          ((cechUnit (i : X.left.Opens)).app G) =
      F.map ((cechUnit (i : X.left.Opens)).app G) ≫
        (openComparison R X Y F hF i.2 ((openKernelSystem R X Y F hF).chartKernelIso i.2)).hom.app
          ((qcohRestrict (i : X.left.Opens).ι).obj G) :=
  (isLimitCech R X Y F hF G).fac _ (.left i)

/-- Morphisms into `F_K(G)` are determined by their composites with the legs at the affine
opens of `X`. -/
theorem integralTransform_hom_ext (G : Scheme.QuasicoherentModules X.left)
    {T : Scheme.QuasicoherentModules Y.left}
    {a b : T ⟶ (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).obj G}
    (h : ∀ i : X.left.affineOpens,
      a ≫ (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
          ((cechUnit (i : X.left.Opens)).app G) =
        b ≫ (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
          ((cechUnit (i : X.left.Opens)).app G)) : a = b := by
  refine (isLimitCech R X Y F hF G).hom_ext ?_
  rintro (i | p)
  · exact h i
  · exact comp_eq_comp_of_comp_eq_comp (h p.1)
      (((quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).mapCone
        (cechMultifork (Subtype.val : X.left.affineOpens → X.left.Opens) G)).w
          (multicospanFst p))

/-- **The natural transformation `t : F ⟶ F_K`** of Tag 0GPA, for the kernel `K` glued from the
kernels of the affine opens:  at `G` it is the map into the limit `F_K(G)` of the Čech diagram of
`G` for the affine opens of `X` whose components are `F(G) ⟶ F((U ↪ X)_*(G|_U)) ≅
F_K((U ↪ X)_*(G|_U))`. -/
def kernelTransform :
    F ⟶ quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued where
  app := kernelTransformApp R X Y F hF
  naturality G G' φ := integralTransform_hom_ext R X Y F hF G' fun i => by
    have n1 := (cechUnit (i : X.left.Opens)).naturality φ
    simp only [Functor.id_map] at n1
    have nψ := (openComparison R X Y F hF i.2
      ((openKernelSystem R X Y F hF).chartKernelIso i.2)).hom.naturality
        ((qcohRestrict (i : X.left.Opens).ι).map φ)
    simp only [Functor.comp_map] at nψ
    exact kernelTransform_naturality_chase F
      (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued) φ _ _ _ n1 _ _
      nψ _ _ (kernelTransformApp_comp R X Y F hF G i) (kernelTransformApp_comp R X Y F hF G' i)

/-- The unit of the restriction adjunction along an open immersion is an isomorphism at a
direct image. -/
theorem isIso_restrictAdjunction_unit_app_pushforward {S : Scheme.{u}} (U : S.Opens)
    (N : U.toScheme.Modules) :
    IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app
      ((Scheme.Modules.pushforward U.ι).obj N)) := by
  have tri := (Scheme.Modules.restrictAdjunction U.ι).right_triangle_components N
  have : IsIso ((Scheme.Modules.restrictAdjunction U.ι).counit.app N) :=
    NatIso.isIso_app_of_isIso _ _
  have : IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app
      ((Scheme.Modules.pushforward U.ι).obj N) ≫
        (Scheme.Modules.pushforward U.ι).map
          ((Scheme.Modules.restrictAdjunction U.ι).counit.app N)) := by
    rw [tri]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward U.ι).map
    ((Scheme.Modules.restrictAdjunction U.ι).counit.app N))

/-- **`t` is an isomorphism on direct images from an affine open.** -/
theorem isIso_kernelTransform_app_pushforward (k : X.left.affineOpens)
    (N : Scheme.QuasicoherentModules (k : X.left.Opens).toScheme) :
    IsIso ((kernelTransform R X Y F hF).app
      ((quasicoherentPushforward (k : X.left.Opens).ι).obj N)) := by
  let G := (quasicoherentPushforward (k : X.left.Opens).ι).obj N
  have : IsIso ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι.map
      ((cechUnit (k : X.left.Opens)).app G)) := by
    change IsIso ((cechUnit (k : X.left.Opens)).app G).hom
    rw [cechUnit_app_hom]
    exact isIso_restrictAdjunction_unit_app_pushforward _ N.obj
  have : IsIso ((cechUnit (k : X.left.Opens)).app G) :=
    isIso_of_reflects_iso _ (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).ι
  have : IsIso (kernelTransformApp R X Y F hF G ≫
      (quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
        ((cechUnit (k : X.left.Opens)).app G)) := by
    rw [kernelTransformApp_comp R X Y F hF G k]
    exact IsIso.comp_isIso' (Functor.map_isIso F _)
      (Iso.isIso_hom ((openComparison R X Y F hF k.2
        ((openKernelSystem R X Y F hF).chartKernelIso k.2)).app
          ((qcohRestrict (k : X.left.Opens).ι).obj G)))
  exact IsIso.of_isIso_comp_right (kernelTransformApp R X Y F hF G)
    ((quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF).glued).map
      ((cechUnit (k : X.left.Opens)).app G))

/-- **`t` is an isomorphism on direct images along a morphism of affine schemes into an affine
open.** -/
theorem isIso_kernelTransform_app_pushforward_of_eq (k : X.left.affineOpens) {Z : Scheme.{u}}
    (g : Z ⟶ X.left) [QuasiCompact g] [QuasiSeparated g] (g' : Z ⟶ (k : X.left.Opens).toScheme)
    [QuasiCompact g'] [QuasiSeparated g'] (hg : g' ≫ (k : X.left.Opens).ι = g)
    (M : Scheme.QuasicoherentModules Z) :
    IsIso ((kernelTransform R X Y F hF).app ((quasicoherentPushforward g).obj M)) := by
  subst hg
  exact isIso_app_of_iso_of_isIso_app (kernelTransform R X Y F hF)
    ((quasicoherentPushforwardComp g' (k : X.left.Opens).ι).app M).symm
    (isIso_kernelTransform_app_pushforward R X Y F hF k ((quasicoherentPushforward g').obj M))

/-- **`t` is an isomorphism on `f_*(W ↪ X')_* M` when `W` lies over an affine open of `X`.** -/
theorem isIso_kernelTransform_app_pushforward_pushforward {X' : Scheme.{u}} (f : X' ⟶ X.left)
    [QuasiCompact f] [QuasiSeparated f] (k : X.left.affineOpens) {W : X'.Opens}
    (hW : W ≤ f ⁻¹ᵁ (k : X.left.Opens)) [IsAffine W.toScheme]
    [IsAffine (f ⁻¹ᵁ (k : X.left.Opens)).toScheme] [QuasiCompact W.ι]
    (M : Scheme.QuasicoherentModules W.toScheme) :
    IsIso ((kernelTransform R X Y F hF).app
      ((quasicoherentPushforward f).obj ((quasicoherentPushforward W.ι).obj M))) := by
  have : IsAffine (k : X.left.Opens).toScheme := k.2
  have hg :
      (X'.homOfLE hW ≫ f ∣_ (k : X.left.Opens)) ≫ (k : X.left.Opens).ι = W.ι ≫ f := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  exact isIso_app_of_iso_of_isIso_app (kernelTransform R X Y F hF)
    ((quasicoherentPushforwardComp W.ι f).app M)
    (isIso_kernelTransform_app_pushforward_of_eq R X Y F hF k (W.ι ≫ f)
      (X'.homOfLE hW ≫ f ∣_ (k : X.left.Opens)) hg M)

end Concrete

/-! ### Tag 0GPA -/

section Main

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)

attribute [local instance] isAffineHom_left_of_isAffine_left isAffineHom_ι_affineOpens
  isAffineHom_ι_affineOpens_inf

/-- **`t` is an isomorphism on direct images from affine sources**:  for a right exact `F` and
every morphism `f : X' ⟶ X` over `R` with `X'` affine, `t ∘ f_* : F ∘ f_* ⟶ F_K ∘ f_*` is an
isomorphism. -/
theorem isIso_whiskerLeft_kernelTransform [CompactSpace X.left]
    [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (hF : rightExactLinearCoproductFunctor R X Y F) {X' : Over (Spec (.of R))} [IsAffine X'.left]
    (f : X' ⟶ X) :
    letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
    IsIso (Functor.whiskerLeft (quasicoherentPushforward f.left)
      (kernelTransform R X Y F
        (affineOpenRightExactLinearCoproductFunctor_of_rightExact R X Y F hF))) := by
  let : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
  let hF' := affineOpenRightExactLinearCoproductFunctor_of_rightExact R X Y F hF
  let V : X.left.affineOpens → X'.left.Opens := fun i => f.left ⁻¹ᵁ (i : X.left.Opens)
  have hV : TopologicalSpace.IsOpenCover V := by
    simpa [TopologicalSpace.IsOpenCover, V, Scheme.Hom.preimage_iSup] using
      congrArg (fun W : X.left.Opens => f.left ⁻¹ᵁ W) (iSup_affineOpens_eq_top X.left)
  have hVa : ∀ i, IsAffine (V i).toScheme := fun i => IsAffineOpen.preimage i.2 f.left
  have hVb : ∀ i j, IsAffine (V i ⊓ V j).toScheme := fun i j =>
    IsAffineOpen.preimage (IsAffineOpen.inf i.2 j.2) f.left
  have : ∀ i, QuasiCompact (V i).ι := fun i => by have := hVa i; infer_instance
  have : ∀ i j, QuasiCompact (V i ⊓ V j).ι := fun i j => by have := hVb i j; infer_instance
  let G : (rightExactLinearCoproductFunctor R X' Y).FullSubcategory :=
    ⟨quasicoherentPushforward f.left ⋙ F,
      rightExactLinearCoproductFunctor_comp_quasicoherentPushforward R X Y F hF f⟩
  let e : quasicoherentPushforward f.left ⋙ F ≅ quasicoherentIntegralTransform R X' Y
      ((integralTransformQcohEquivalence R X' Y).inverse.obj G) :=
    ((ObjectProperty.ι (rightExactLinearCoproductFunctor R X' Y)).mapIso
      ((integralTransformQcohEquivalence R X' Y).counitIso.app G)).symm
  rw [NatTrans.isIso_iff_isIso_app]
  intro H
  have hP : IsLimit ((quasicoherentPushforward f.left ⋙ F).mapCone (cechMultifork V H)) :=
    IsLimit.mapConeEquiv e.symm
      (isLimitIntegralTransformCechMultifork R X' Y _ V hV H)
  have hQ : IsLimit ((quasicoherentPushforward f.left ⋙
      quasicoherentIntegralTransform R X Y (openKernelSystem R X Y F hF').glued).mapCone
        (cechMultifork V H)) :=
    IsLimit.mapConeEquiv (quasicoherentIntegralTransformSourceChangeIso' R X X' Y f
        (openKernelSystem R X Y F hF').glued).symm
      (isLimitIntegralTransformCechMultifork R X' Y
        (sourceChangeKernel R X X' Y f (openKernelSystem R X Y F hF').glued) V hV H)
  refine isIso_app_pt_of_isLimit _ (cechMultifork V H) hP hQ ?_
  rintro (i | p)
  · have := hVa i
    exact isIso_kernelTransform_app_pushforward_pushforward R X Y F hF' f.left i (le_refl (V i))
      ((qcohRestrict (V i).ι).obj H)
  · have := hVa p.1
    have := hVb p.1 p.2
    exact isIso_kernelTransform_app_pushforward_pushforward R X Y F hF' f.left p.1
      (inf_le_left : V p.1 ⊓ V p.2 ≤ V p.1) ((qcohRestrict (V p.1 ⊓ V p.2).ι).obj H)

/-- **Tag 0GPA.**  Let `R` be a ring, let `X` and `Y` be schemes over `R` with `X` quasi-compact
with affine diagonal, and let `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` be `R`-linear, right exact and
commute with arbitrary direct sums.  Then there are a quasi-coherent module `K` on `X ×_R Y` and a
natural transformation `t : F ⟶ F_K` such that `t ∘ f_* : F ∘ f_* ⟶ F_K ∘ f_*` is an
isomorphism for every morphism `f : X' ⟶ X` whose source is an affine scheme.

The kernel is `AlgebraicGeometry.AffineChartKernels.glued` of
`AlgebraicGeometry.openKernelSystem`, glued from the kernels of `F ∘ j_{U,*}` over the affine
opens `U` of `X`, and `t` is `AlgebraicGeometry.kernelTransform`. -/
@[stacks 0GPA]
theorem exists_kernel_natTrans_isIso_whiskerLeft_pushforward [CompactSpace X.left]
    [IsAffineHom (pullback.diagonal (terminal.from X.left))]
    (hF : rightExactLinearCoproductFunctor R X Y F) :
    ∃ (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
      (t : F ⟶ quasicoherentIntegralTransform R X Y K),
      ∀ (X' : Scheme.{u}) [IsAffine X'] (f : X' ⟶ X.left),
        letI : IsAffineHom f :=
          Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source f
        IsIso (Functor.whiskerLeft (quasicoherentPushforward f) t) := by
  have : QuasiSeparated (terminal.from X.left) := ⟨inferInstance⟩
  have : QuasiSeparatedSpace X.left :=
    quasiSeparatedSpace_of_quasiSeparated (terminal.from X.left)
  let hF' := affineOpenRightExactLinearCoproductFunctor_of_rightExact R X Y F hF
  refine ⟨(openKernelSystem R X Y F hF').glued, kernelTransform R X Y F hF', fun X' hX' f => ?_⟩
  have : IsAffine (Over.mk (f ≫ X.hom)).left := hX'
  exact isIso_whiskerLeft_kernelTransform R X Y F hF (X' := Over.mk (f ≫ X.hom))
    (Over.homMk f rfl)

end Main

end AlgebraicGeometry

end
