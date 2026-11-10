module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimitUnivLE
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.Restriction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BigSheafifyZariskiSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisBaseChangeAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekAbelianExact
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekTypeExactness

/-!
# The presheaf underlying `i_!` of a crystal, locally over a morphism to `Cris(X/S)`

The module-level lower shriek `i_! : Mod(Cris(X/S)) ⥤ Mod(CRIS(X/S))` of [Stacks, Tag 07IJ],
`...SmallSite.moduleLowerShriek`, is the sheafification of Mathlib's presheaf pullback, and by
`Stacks.PullbackColimitUnivLE.pullbackIdIso` that presheaf is the objectwise colimit

`L(B) = colim_{(A, B ⟶ i A)} 𝒪(B) ⊗_{𝒪(A)} ℱ(A)`

over the comma category of `B` under the image of the small site.  This file computes `L` locally
on an object `B` of `CRIS(X/S)` which comes with a morphism `τ : B ⟶ i A` to an object `A` of
`Cris(X/S)` with affine ambient scheme, for `ℱ` a locally quasi-coherent crystal (lifted to the
module universe `u + 1` by `...SmallSite.moduleULift`).  Writing `B|_W` for the restriction of `B`
to an open `W` of its ambient scheme and `τ_W : B|_W ⟶ i A` for the restriction of `τ`:

* **local surjectivity** (`mem_closure_germ_restrictOpenLE`): every section of `L` over `B|_W`
  becomes, on a neighbourhood of each point of `W`, a sum of germs of pure tensors at the index
  `(A, τ_W)`;
* **local injectivity** (`exists_restrictOpenLE_diagramRestrict_eq_zero`): an element of
  `𝒪(B|_W) ⊗_{𝒪(A)} ℱ(A)` whose germ at `(A, τ_W)` vanishes in `L(B|_W)` vanishes on a
  neighbourhood of each point of `W`.

The index category is filtered, because `Cris(X/S)` has products of pairs and equalizers which
the inclusion preserves ([Stacks, Tag 07I9]), so the colimit has the element calculus of a
filtered colimit.  The two facts are the source's: a germ at an index `(A₁, σ)` is compared with
the index `(A, τ)` through the product `A₁ × A`, restricted to an affine open of its ambient
scheme containing the image of a given point, over which the crystal is the base change of its
sections over `A` (`...SmallSite.bijective_crisBaseChangeAlong`).

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Stacks.PullbackColimitUnivLE

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The colimit model of `i_!` -/

/-- The structure presheaf of commutative rings of `CRIS(X/S)`. -/
abbrev crisCommRing (S : GlobalCrystallineSituation.{u}) : (Thickening S)ᵒᵖ ⥤ CommRingCat.{u} :=
  GlobalCrystallineSituation.structureSheaf S

/-- **The presheaf of modules underlying `i_! M`, as an objectwise colimit**: its sections over an
object `B` of `CRIS(X/S)` are `colim_{(A, B ⟶ i A)} 𝒪(B) ⊗_{𝒪(A)} M(A)`. -/
abbrev lowerShriekModel (M : ModuleSheaf S) :
    PresheafOfModules.{u + 1} (crisCommRing S ⋙ forget₂ CommRingCat RingCat) :=
  Stacks.PullbackColimitUnivLE.obj (CrystallineThickening.ι S) (crisCommRing S) M.val

/-- **The comparison of the colimit model with the sheaf `i_! M`**: the inverse of
`Stacks.PullbackColimitUnivLE.pullbackIdIso` followed by the sheafification unit. -/
def lowerShriekModelToSheaf (M : ModuleSheaf S) :
    (lowerShriekModel M).presheaf ⟶ ((moduleLowerShriek S).obj M).val.presheaf :=
  (PresheafOfModules.toPresheaf _).map
      ((Stacks.PullbackColimitUnivLE.pullbackIdIso (CrystallineThickening.ι S)
        (crisCommRing S)).inv.app M.val) ≫
    toSheafify (topology S) _

/-- **The index category of the colimit is filtered or empty**: `Cris(X/S)` has products of pairs
and equalizers, and the inclusion into `CRIS(X/S)` preserves them. -/
theorem isFilteredOrEmpty_index (B : Thickening S) :
    IsFilteredOrEmpty (CostructuredArrow (CrystallineThickening.ι S).op (op B)) :=
  have := CrystallineThickening.hasEqualizers_crystallineThickening S
  have := CrystallineThickening.ι_preservesEqualizers S
  Stacks.Sites.LowerShriek.costructuredArrow_isFilteredOrEmpty _ (op B)

/-- **The index category of the colimit is filtered** as soon as it is nonempty. -/
theorem isFiltered_index {B : Thickening S}
    (T : CostructuredArrow (CrystallineThickening.ι S).op (op B)) :
    IsFiltered (CostructuredArrow (CrystallineThickening.ι S).op (op B)) :=
  have := isFilteredOrEmpty_index B
  have : Nonempty (CostructuredArrow (CrystallineThickening.ι S).op (op B)) := ⟨T⟩
  { }

/-! ### Two factorizations -/

/-- **A morphism into the image of a product of `Cris(X/S)`**, from a morphism into the image of
each factor: the inclusion preserves products of pairs. -/
def prodLiftι {V : Thickening S} {A₁ A₂ : CrystallineThickening S}
    (σ₁ : V ⟶ (CrystallineThickening.ι S).obj A₁) (σ₂ : V ⟶ (CrystallineThickening.ι S).obj A₂) :
    V ⟶ (CrystallineThickening.ι S).obj (A₁ ⨯ A₂) :=
  prod.lift σ₁ σ₂ ≫ (PreservesLimitPair.iso (CrystallineThickening.ι S) A₁ A₂).inv

/-- `prodLiftι` followed by the first projection. -/
@[reassoc (attr := simp)]
theorem prodLiftι_fst {V : Thickening S} {A₁ A₂ : CrystallineThickening S}
    (σ₁ : V ⟶ (CrystallineThickening.ι S).obj A₁) (σ₂ : V ⟶ (CrystallineThickening.ι S).obj A₂) :
    prodLiftι σ₁ σ₂ ≫ (CrystallineThickening.ι S).map prod.fst = σ₁ := by
  rw [prodLiftι, Category.assoc, PreservesLimitPair.iso_inv_fst, prod.lift_fst]

/-- `prodLiftι` followed by the second projection. -/
@[reassoc (attr := simp)]
theorem prodLiftι_snd {V : Thickening S} {A₁ A₂ : CrystallineThickening S}
    (σ₁ : V ⟶ (CrystallineThickening.ι S).obj A₁) (σ₂ : V ⟶ (CrystallineThickening.ι S).obj A₂) :
    prodLiftι σ₁ σ₂ ≫ (CrystallineThickening.ι S).map prod.snd = σ₂ := by
  rw [prodLiftι, Category.assoc, PreservesLimitPair.iso_inv_snd, prod.lift_snd]

/-- **A morphism from a restriction into the image of `Cris(X/S)` factors, near any point, through
the restriction of its target to an affine open.**  Given `σ : B|_W ⟶ i A₂` and a point `p` of
`W`, there is an open `W' ⊆ W` containing `p` and an affine open `V₂` of the ambient scheme of
`A₂` such that `σ` restricted to `W'` factors through `i (A₂|_{V₂})`. -/
theorem exists_restrictOpen_affine_lift (B : Thickening S)
    (W : B.thickening.target.scheme.Opens) {A₂ : CrystallineThickening S}
    (σ : B.restrictOpen W ⟶ (CrystallineThickening.ι S).obj A₂)
    (p : B.thickening.target.scheme) (hp : p ∈ W) :
    ∃ (W' : B.thickening.target.scheme.Opens) (h : W' ≤ W) (_ : p ∈ W')
      (V₂ : A₂.obj.thickening.target.scheme.Opens) (_ : IsAffineOpen V₂)
      (σ' : B.restrictOpen W' ⟶ (CrystallineThickening.ι S).obj (A₂.restrictOpen V₂)),
      σ' ≫ (CrystallineThickening.ι S).map (A₂.restrictOpenHom V₂) =
        B.restrictOpenLE h ≫ σ := by
  let p' : W.toScheme := ⟨p, hp⟩
  obtain ⟨_, ⟨V₂, hV₂, rfl⟩, hq, -⟩ :=
    A₂.obj.thickening.target.scheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (σ.targetHom.hom.base p')) isOpen_univ
  let W'' : W.toScheme.Opens := σ.targetHom.hom ⁻¹ᵁ V₂
  let W' : B.thickening.target.scheme.Opens := W.ι ''ᵁ W''
  have h : W' ≤ W := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hr : ∀ z : (B.restrictOpen W').thickening.target.scheme,
      (B.restrictOpenLE h ≫ σ).targetHom.hom.base z ∈ V₂ := by
    intro z
    obtain ⟨y, hy, hyz⟩ := z.2
    have hz : (B.thickening.target.scheme.homOfLE h).base z = y :=
      W.ι.isOpenEmbedding.injective
        ((congrArg (fun k : W'.toScheme ⟶ B.thickening.target.scheme ↦ k.base z)
          (Scheme.homOfLE_ι B.thickening.target.scheme h)).trans hyz.symm)
    change σ.targetHom.hom.base ((B.thickening.target.scheme.homOfLE h).base z) ∈ V₂
    rwa [hz]
  exact ⟨W', h, ⟨p', hq, rfl⟩, V₂, hV₂, Thickening.liftRestrictOpen _ V₂ hr,
    Thickening.liftRestrictOpen_comp _ V₂ hr⟩

/-! ### The transitions of the colimit between affine indices -/

/-- The universe lift of a sheaf of `𝒪_{X/S}`-modules, as the presheaf of modules the colimit
model is built from. -/
abbrev ulModel (F : SheafOfModules.{u} (structureSheaf S)) :
    PresheafOfModules.{u + 1}
      (((CrystallineThickening.ι S).op ⋙ crisCommRing S) ⋙ forget₂ CommRingCat RingCat) :=
  ((moduleULift S).obj F).val

/-- A section of `ℱ`, read as a section of its universe lift. -/
abbrev upSection (F : SheafOfModules.{u} (structureSheaf S)) {A : CrystallineThickening S}
    (s : F.val.obj (op A)) : (ulModel F).obj (op A) :=
  ULift.up s

/-- The restriction map of `𝒪_{X/S}` along an index, with its source read as the section ring of
the object of `Cris(X/S)`. -/
def ringIdx {A : CrystallineThickening S} {U : (Thickening S)ᵒᵖ}
    (h : (CrystallineThickening.ι S).op.obj (op A) ⟶ U) :
    crysSheafRing S A.obj →+* (crisCommRing S).obj U :=
  ((crisCommRing S).map h).hom

section Transition

variable (F : SheafOfModules.{u} (structureSheaf S)) {U : (Thickening S)ᵒᵖ}
  {A₀ A₁ : CrystallineThickening S} (k : A₁ ⟶ A₀)
  (h₀ : (CrystallineThickening.ι S).op.obj (op A₀) ⟶ U)
  (h₁ : (CrystallineThickening.ι S).op.obj (op A₁) ⟶ U)
  (e : (CrystallineThickening.ι S).op.map k.op ≫ h₁ = h₀)

include e in
/-- The ring maps of two indices related by `k` are related by the restriction along `k`. -/
lemma ringIdx_comp (a : crysSheafRing S A₀.obj) :
    ringIdx h₀ a = ringIdx h₁ (crysSheafRingMap k.hom a) := by
  rw [ringIdx, ← e, Functor.map_comp]
  rfl

/-- The bilinear datum of `transitionInvAux`. -/
def transitionInvBil :
    ringAlong k.hom →+ (F.val.obj (op A₀) →+
      diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk h₀)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ tmul ((crisCommRing S).map h₀).hom (ringIdx h₁ (siteRingAlong k.hom t))
        (upSection F s))
      (fun s s' ↦ tmul_add _ _ (upSection F s) (upSection F s')))
    (fun t t' ↦ by
      refine AddMonoidHom.ext fun s ↦ ?_
      change tmul _ (ringIdx h₁ (siteRingAlong k.hom (t + t'))) _ =
        tmul _ (ringIdx h₁ (siteRingAlong k.hom t)) _ +
          tmul _ (ringIdx h₁ (siteRingAlong k.hom t')) _
      rw [siteRingAlong_add, map_add, tmul_eq_smul _ (_ + _), add_smul, ← tmul_eq_smul,
        ← tmul_eq_smul])

include e in
/-- **The tensor product `𝒪(A₁) ⊗_{𝒪(A₀)} ℱ(A₀)` mapped into the term of the colimit at the index
`(A₀, h₀)`**, `t ⊗ s ↦ h₁(t) ⊗ s`. -/
def transitionInvAux :
    ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀) →+
      diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk h₀) :=
  TensorProduct.liftAddHom (transitionInvBil F k h₀ h₁) (fun b t s ↦ by
    change tmul _ (ringIdx h₁ (siteRingAlong k.hom (b • t))) (upSection F s) =
      tmul _ (ringIdx h₁ (siteRingAlong k.hom t)) (upSection F (b • s))
    rw [siteRingAlong_smul, map_mul, ← ringIdx_comp k h₀ h₁ e]
    change _ = tmul _ _
      ((show ↑((crisCommRing S).obj ((CrystallineThickening.ι S).op.obj (op A₀))) from b) •
        upSection F s)
    rw [tmul_smul_right, mul_comm]
    rfl)

/-- `transitionInvAux` on a pure tensor. -/
lemma transitionInvAux_tmul (t : ringAlong k.hom) (s : F.val.obj (op A₀)) :
    transitionInvAux F k h₀ h₁ e (t ⊗ₜ s) =
      tmul ((crisCommRing S).map h₀).hom (ringIdx h₁ (siteRingAlong k.hom t)) (upSection F s) :=
  TensorProduct.liftAddHom_tmul _ _ t s

/-- `transitionInvAux` is compatible with the scalar actions. -/
lemma transitionInvAux_smul (c : ringAlong k.hom)
    (z : ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀)) :
    transitionInvAux F k h₀ h₁ e (c • z) =
      ringIdx h₁ (siteRingAlong k.hom c) • transitionInvAux F k h₀ h₁ e z := by
  induction z using TensorProduct.inductionOn with
  | tmul t s =>
      rw [TensorProduct.smul_tmul', transitionInvAux_tmul, transitionInvAux_tmul, smul_eq_mul,
        smul_tmul]
      congr 1
      exact map_mul (ringIdx h₁) (siteRingAlong k.hom c) (siteRingAlong k.hom t)
  | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]

/-- `crisBaseChangeAlong` is compatible with the scalar actions. -/
lemma crisBaseChangeAlong_smul (c : ringAlong k.hom)
    (z : ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀)) :
    crisBaseChangeAlong F k (c • z) = siteRingAlong k.hom c • crisBaseChangeAlong F k z := by
  induction z using TensorProduct.inductionOn with
  | tmul t s =>
      rw [TensorProduct.smul_tmul', crisBaseChangeAlong_tmul, crisBaseChangeAlong_tmul,
        smul_smul]
      rfl
  | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]

variable [IsAffine A₀.obj.thickening.target.scheme] [IsAffine A₁.obj.thickening.target.scheme]
  (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F)

include hF hcrys in
/-- The inverse of the base change of sections is semilinear. -/
lemma crisBaseChangeAlongEquiv_symm_smul (c : ringAlong k.hom) (y : F.val.obj (op A₁)) :
    (crisBaseChangeAlongEquiv F k hF hcrys).symm (siteRingAlong k.hom c • y) =
      c • (crisBaseChangeAlongEquiv F k hF hcrys).symm y := by
  apply (crisBaseChangeAlongEquiv F k hF hcrys).injective
  rw [AddEquiv.apply_symm_apply, crisBaseChangeAlongEquiv_apply, crisBaseChangeAlong_smul,
    ← crisBaseChangeAlongEquiv_apply F k hF hcrys, AddEquiv.apply_symm_apply]

include hF hcrys in
/-- The inverse of the base change of sections on a restricted section is `1 ⊗ s`. -/
lemma crisBaseChangeAlongEquiv_symm_restrict (s : F.val.obj (op A₀)) :
    (crisBaseChangeAlongEquiv F k hF hcrys).symm (crysSiteRestrict F k s) =
      (1 : ringAlong k.hom) ⊗ₜ s := by
  apply (crisBaseChangeAlongEquiv F k hF hcrys).injective
  rw [AddEquiv.apply_symm_apply, crisBaseChangeAlongEquiv_apply, crisBaseChangeAlong_tmul]
  exact (one_smul ((structureSheaf S).obj.obj (op A₁)) _).symm

/-- **The inverse transition, on sections**: a section of the lift of `ℱ` over `A₁` is written,
by the crystal property, as a base change of sections over `A₀`, and carried to the term of the
colimit at `(A₀, h₀)`. -/
def transitionInvLin : (ulModel F).obj (op A₁) ⟶
    (ModuleCat.restrictScalars ((crisCommRing S).map h₁).hom).obj
      (diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk h₀)) :=
  letI : Module ((structureSheaf S).obj.obj (op A₁))
      ((ModuleCat.restrictScalars ((crisCommRing S).map h₁).hom).obj
        (diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
          (CostructuredArrow.mk h₀))) :=
    inferInstanceAs (Module ((crisCommRing S).obj ((CrystallineThickening.ι S).op.obj (op A₁)))
      ((ModuleCat.restrictScalars ((crisCommRing S).map h₁).hom).obj
        (diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
          (CostructuredArrow.mk h₀))))
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars ((crisCommRing S).map h₁).hom).obj
      (diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk h₀)))
    { toFun := fun m ↦ transitionInvAux F k h₀ h₁ e
        ((crisBaseChangeAlongEquiv F k hF hcrys).symm m.down)
      map_add' := fun m m' ↦ by
        change transitionInvAux F k h₀ h₁ e
            ((crisBaseChangeAlongEquiv F k hF hcrys).symm (m.down + m'.down)) = _
        rw [map_add, map_add]
        rfl
      map_smul' := fun c m ↦ by
        change transitionInvAux F k h₀ h₁ e ((crisBaseChangeAlongEquiv F k hF hcrys).symm
            (siteRingAlong k.hom (ringAlongSection k.hom c) • m.down)) = _
        rw [crisBaseChangeAlongEquiv_symm_smul, transitionInvAux_smul]
        rfl }

/-- `transitionInvLin` on a restricted section `k^* s` is `1 ⊗ s`. -/
lemma transitionInvLin_restrict (s : F.val.obj (op A₀)) :
    transitionInvLin F k h₀ h₁ e hF hcrys ((ulModel F).restrictₛₗ k.op (upSection F s)) =
      tmul ((crisCommRing S).map h₀).hom 1 (upSection F s) := by
  change transitionInvAux F k h₀ h₁ e
      ((crisBaseChangeAlongEquiv F k hF hcrys).symm (crysSiteRestrict F k s)) = _
  rw [crisBaseChangeAlongEquiv_symm_restrict, transitionInvAux_tmul,
    show siteRingAlong k.hom (1 : ringAlong k.hom) = 1 from rfl, map_one]

/-- **The inverse transition between two indices with affine objects**: the term of the colimit
at `(A₁, h₁)` is mapped back to the term at `(A₀, h₀)`, for `k : A₁ ⟶ A₀` with
`h₀ = k ≫ h₁`.  On `r ⊗ k^* s` it is `r ⊗ s`, by `transitionInv_tmul_restrict`. -/
def transitionInv :
    diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk h₁) ⟶
      diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk h₀) :=
  ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} ((crisCommRing S).map h₁).hom).homEquiv
    _ _).symm (transitionInvLin F k h₀ h₁ e hF hcrys)

/-- `transitionInv` on `r ⊗ k^* s` is `r ⊗ s`. -/
lemma transitionInv_tmul_restrict (r : (crisCommRing S).obj U) (s : F.val.obj (op A₀)) :
    transitionInv F k h₀ h₁ e hF hcrys
        (tmul ((crisCommRing S).map h₁).hom r ((ulModel F).restrictₛₗ k.op (upSection F s))) =
      tmul ((crisCommRing S).map h₀).hom r (upSection F s) := by
  rw [tmul_eq_smul _ r, map_smul, transitionInv, homEquiv_symm_apply_tmul,
    transitionInvLin_restrict, smul_tmul, mul_one]

/-- The transition along `k`, as a morphism of the index category. -/
abbrev transitionHom : CostructuredArrow.mk h₀ ⟶ CostructuredArrow.mk h₁ :=
  CostructuredArrow.homMk (f := CostructuredArrow.mk h₀) (f' := CostructuredArrow.mk h₁) k.op e

omit [IsAffine A₀.obj.thickening.target.scheme] [IsAffine A₁.obj.thickening.target.scheme] in
/-- The transition along `k` undoes `transitionInvAux`, up to the base change of sections. -/
lemma diagramMap_transitionInvAux
    (z : ringAlong k.hom ⊗[crysSheafRing S A₀.obj] F.val.obj (op A₀)) :
    diagramMap (CrystallineThickening.ι S) (crisCommRing S) (ulModel F) (transitionHom k h₀ h₁ e)
        (transitionInvAux F k h₀ h₁ e z) =
      tmul ((crisCommRing S).map h₁).hom 1 (upSection F (crisBaseChangeAlong F k z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul t s =>
      rw [transitionInvAux_tmul, crisBaseChangeAlong_tmul]
      exact (tmul_one_smul ((crisCommRing S).map h₁).hom
        (show ↑((crisCommRing S).obj ((CrystallineThickening.ι S).op.obj (op A₁))) from
          siteRingAlong k.hom t) ((ulModel F).restrictₛₗ k.op (upSection F s))).symm
  | add z z' hz hz' =>
      rw [map_add, map_add, hz, hz', map_add]
      exact (tmul_one_add _ _ _).symm

include hF hcrys in
/-- **The transitions of the colimit between two indices whose objects have affine ambient
schemes are bijective**, for a locally quasi-coherent crystal: the crystal property identifies
the sections over the source with the base change of the sections over the target. -/
theorem bijective_diagramMap_transitionHom :
    Function.Bijective (diagramMap (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
      (transitionHom k h₀ h₁ e)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨transitionInv F k h₀ h₁ e hF hcrys, fun y ↦ ?_, fun y ↦ ?_⟩
  · have h : diagramMap (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
          (transitionHom k h₀ h₁ e) ≫ transitionInv F k h₀ h₁ e hF hcrys = 𝟙 _ :=
      extendScalars_hom_ext _ fun m ↦ transitionInv_tmul_restrict F k h₀ h₁ e hF hcrys 1 m.down
    exact ConcreteCategory.congr_hom h y
  · have h : transitionInv F k h₀ h₁ e hF hcrys ≫
          diagramMap (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
            (transitionHom k h₀ h₁ e) = 𝟙 _ := by
      refine extendScalars_hom_ext _ fun m ↦ ?_
      have h2 : transitionInv F k h₀ h₁ e hF hcrys (tmul ((crisCommRing S).map h₁).hom 1 m) =
          transitionInvAux F k h₀ h₁ e ((crisBaseChangeAlongEquiv F k hF hcrys).symm m.down) :=
        homEquiv_symm_apply_tmul _ (transitionInvLin F k h₀ h₁ e hF hcrys) m
      change diagramMap (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
          (transitionHom k h₀ h₁ e) (transitionInv F k h₀ h₁ e hF hcrys
            (tmul ((crisCommRing S).map h₁).hom 1 m)) = tmul ((crisCommRing S).map h₁).hom 1 m
      rw [h2, diagramMap_transitionInvAux F k h₀ h₁ e, ← crisBaseChangeAlongEquiv_apply F k
        hF hcrys, AddEquiv.apply_symm_apply]
      rfl
    exact ConcreteCategory.congr_hom h y

end Transition

/-! ### Local surjectivity and local injectivity over a morphism to `Cris(X/S)` -/

section Local

variable (F : SheafOfModules.{u} (structureSheaf S)) {B : Thickening S}
  {A : CrystallineThickening S} (τ : B ⟶ (CrystallineThickening.ι S).obj A)

/-- The index `(A, τ_W)` of the colimit over the restriction of `B` to an open `W` of its ambient
scheme, `τ_W` being the restriction of `τ`. -/
abbrev tauIdx (W : B.thickening.target.scheme.Opens) :
    (CrystallineThickening.ι S).op.obj (op A) ⟶ op (B.restrictOpen W) :=
  (B.restrictOpenHom W ≫ τ).op

/-- The index `(A, τ_W)` restricted to `W' ⊆ W` is the index `(A, τ_{W'})`. -/
lemma tauIdx_restrictOpenLE {W W' : B.thickening.target.scheme.Opens} (h : W' ≤ W) :
    tauIdx τ W ≫ (B.restrictOpenLE h).op = tauIdx τ W' := by
  rw [tauIdx, tauIdx, ← op_comp, Thickening.restrictOpenLE_restrictOpenHom_assoc]

/-- **The restriction of the term of the colimit at `(A, τ_W)` to the term at `(A, τ_{W'})`**, the
base change along the restriction map `𝒪(B|_W) ⟶ 𝒪(B|_{W'})`. -/
def tauRestrict {W W' : B.thickening.target.scheme.Opens} (h : W' ≤ W) :
    diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk (tauIdx τ W)) ⟶
      (ModuleCat.restrictScalars ((crisCommRing S).map (B.restrictOpenLE h).op).hom).obj
        (diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
          (CostructuredArrow.mk (tauIdx τ W'))) :=
  baseChangeMap ((crisCommRing S).map (tauIdx τ W)).hom ((crisCommRing S).map (tauIdx τ W')).hom
    (σ := ((crisCommRing S).map (B.restrictOpenLE h).op).hom) (ρ := RingHom.id _)
    (fun a ↦ by rw [← tauIdx_restrictOpenLE τ h, Functor.map_comp]; rfl) LinearMap.id

/-- `tauRestrict` on a pure tensor. -/
lemma tauRestrict_tmul {W W' : B.thickening.target.scheme.Opens} (h : W' ≤ W)
    (r : (crisCommRing S).obj (op (B.restrictOpen W))) (m : (ulModel F).obj (op A)) :
    tauRestrict F τ h (tmul ((crisCommRing S).map (tauIdx τ W)).hom r m) =
      tmul ((crisCommRing S).map (tauIdx τ W')).hom
        (((crisCommRing S).map (B.restrictOpenLE h).op).hom r) m := rfl

/-- The restriction of the colimit model from `B|_W` to `B|_{W'}` on the term at `τ_W`. -/
lemma map_restrictOpenLE_ι_tauIdx {W W' : B.thickening.target.scheme.Opens} (h : W' ≤ W)
    (y : diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
      (CostructuredArrow.mk (tauIdx τ W))) :
    (lowerShriekModel ((moduleULift S).obj F)).map (B.restrictOpenLE h).op
        (colimit.ι (diagram (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
          (op (B.restrictOpen W))) (CostructuredArrow.mk (tauIdx τ W)) y) =
      colimit.ι (diagram (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
          (op (B.restrictOpen W'))) (CostructuredArrow.mk (tauIdx τ W')) (tauRestrict F τ h y) :=
  obj_map_ι_mk _ _ _ _ _ _ (tauIdx_restrictOpenLE τ h) y

/-- A lift `σ'` of `b` through `A'|_{V₂}`, with `b` compatible with `τ` along `g`, gives the
index `(A, τ_{W'})` along `A'|_{V₂} ⟶ A`. -/
private lemma map_restrictOpenHom_comp_op_comp_eq_tauIdx {W W' : B.thickening.target.scheme.Opens}
    (h : W' ≤ W) {A' : CrystallineThickening S} (V₂ : A'.obj.thickening.target.scheme.Opens)
    (b : B.restrictOpen W ⟶ (CrystallineThickening.ι S).obj A')
    (σ' : B.restrictOpen W' ⟶ (CrystallineThickening.ι S).obj (A'.restrictOpen V₂))
    (hσ' : σ' ≫ (CrystallineThickening.ι S).map (A'.restrictOpenHom V₂) = B.restrictOpenLE h ≫ b)
    (g : A' ⟶ A) (hg : b ≫ (CrystallineThickening.ι S).map g = B.restrictOpenHom W ≫ τ) :
    (CrystallineThickening.ι S).op.map (A'.restrictOpenHom V₂ ≫ g).op ≫ σ'.op = tauIdx τ W' := by
  apply Quiver.Hom.unop_inj
  change σ' ≫ (CrystallineThickening.ι S).map (A'.restrictOpenHom V₂ ≫ g) =
    B.restrictOpenHom W' ≫ τ
  rw [Functor.map_comp, reassoc_of% hσ', hg, Thickening.restrictOpenLE_restrictOpenHom_assoc]

variable [IsAffine A.obj.thickening.target.scheme]
  (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F)

include hF hcrys in
/-- **Local surjectivity**: a section of the colimit model of `i_!ℱ` over `B|_W` is, near every
point of `W`, the image of an element of the term of the colimit at `(A, τ)`. -/
theorem exists_restrictOpenLE_eq_ι_tauIdx (W : B.thickening.target.scheme.Opens)
    (x : (lowerShriekModel ((moduleULift S).obj F)).obj (op (B.restrictOpen W)))
    (p : B.thickening.target.scheme) (hp : p ∈ W) :
    ∃ (W' : B.thickening.target.scheme.Opens) (h : W' ≤ W) (_ : p ∈ W')
      (w : diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
        (CostructuredArrow.mk (tauIdx τ W'))),
      (lowerShriekModel ((moduleULift S).obj F)).map (B.restrictOpenLE h).op x =
        colimit.ι (diagram (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
          (op (B.restrictOpen W'))) (CostructuredArrow.mk (tauIdx τ W')) w := by
  have := isFiltered_index (CostructuredArrow.mk (tauIdx τ W))
  have := preservesColimit_diagram (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
    (op (B.restrictOpen W))
  obtain ⟨T, y, rfl⟩ := exists_ι_eq (CrystallineThickening.ι S) (crisCommRing S) (ulModel F) x
  obtain ⟨⟨A₁⟩, ⟨⟨⟩⟩, h₁⟩ := T
  obtain ⟨W', h, hpW', V₂, hV₂, σ', hσ'⟩ := exists_restrictOpen_affine_lift B W
    (prodLiftι h₁.unop (B.restrictOpenHom W ≫ τ)) p hp
  have : IsAffine ((A₁ ⨯ A).restrictOpen V₂).obj.thickening.target.scheme := hV₂
  let j : (A₁ ⨯ A).restrictOpen V₂ ⟶ A₁ := (A₁ ⨯ A).restrictOpenHom V₂ ≫ prod.fst
  let k : (A₁ ⨯ A).restrictOpen V₂ ⟶ A := (A₁ ⨯ A).restrictOpenHom V₂ ≫ prod.snd
  have hj : (CrystallineThickening.ι S).op.map j.op ≫ σ'.op = h₁ ≫ (B.restrictOpenLE h).op := by
    apply Quiver.Hom.unop_inj
    change σ' ≫ (CrystallineThickening.ι S).map j = B.restrictOpenLE h ≫ h₁.unop
    rw [Functor.map_comp, reassoc_of% hσ', prodLiftι_fst]
  have hk : (CrystallineThickening.ι S).op.map k.op ≫ σ'.op = tauIdx τ W' :=
    map_restrictOpenHom_comp_op_comp_eq_tauIdx τ h V₂ _ σ' hσ' _ (prodLiftι_snd _ _)
  obtain ⟨w, hw⟩ := (bijective_diagramMap_transitionHom F k (tauIdx τ W') σ'.op hk hF hcrys).2
    (diagramMap (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
      (CostructuredArrow.homMk (f := CostructuredArrow.mk (h₁ ≫ (B.restrictOpenLE h).op))
        (f' := CostructuredArrow.mk σ'.op) j.op hj)
      (baseChangeMap ((crisCommRing S).map h₁).hom
        ((crisCommRing S).map (h₁ ≫ (B.restrictOpenLE h).op)).hom
        (σ := ((crisCommRing S).map (B.restrictOpenLE h).op).hom) (ρ := RingHom.id _)
        (fun a ↦ by rw [Functor.map_comp]; rfl) LinearMap.id y))
  refine ⟨W', h, hpW', w, ?_⟩
  refine (obj_map_ι_mk (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
    (B.restrictOpenLE h).op h₁ _ rfl y).trans
      ((ι_mk_eq (CrystallineThickening.ι S) (crisCommRing S) (ulModel F) _ σ'.op j.op hj _).trans
        ?_)
  exact (congrArg (ConcreteCategory.hom (colimit.ι (diagram (CrystallineThickening.ι S)
      (crisCommRing S) (ulModel F) (op (B.restrictOpen W'))) (CostructuredArrow.mk σ'.op)))
      hw.symm).trans
    (ι_mk_eq (CrystallineThickening.ι S) (crisCommRing S) (ulModel F) _ σ'.op k.op hk w).symm

include hF hcrys in
/-- **Local injectivity**: an element of the term of the colimit at `(A, τ_W)` whose image in the
colimit model of `i_!ℱ` over `B|_W` vanishes, vanishes near every point of `W`. -/
theorem exists_restrictOpenLE_tauRestrict_eq_zero (W : B.thickening.target.scheme.Opens)
    (y : diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
      (CostructuredArrow.mk (tauIdx τ W)))
    (hy : colimit.ι (diagram (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
      (op (B.restrictOpen W))) (CostructuredArrow.mk (tauIdx τ W)) y = 0)
    (p : B.thickening.target.scheme) (hp : p ∈ W) :
    ∃ (W' : B.thickening.target.scheme.Opens) (h : W' ≤ W) (_ : p ∈ W'),
      tauRestrict F τ h y = 0 := by
  have := isFiltered_index (CostructuredArrow.mk (tauIdx τ W))
  have := preservesColimit_diagram (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
    (op (B.restrictOpen W))
  obtain ⟨⟨⟨P⟩, ⟨⟨⟩⟩, b⟩, ψ, hψ⟩ := exists_map_eq_zero_of_ι_eq_zero (CrystallineThickening.ι S)
    (crisCommRing S) (ulModel F) y hy
  obtain ⟨W', h, hpW', V₂, hV₂, σ', hσ'⟩ := exists_restrictOpen_affine_lift B W b.unop p hp
  have : IsAffine (P.restrictOpen V₂).obj.thickening.target.scheme := hV₂
  let k : P.restrictOpen V₂ ⟶ A := P.restrictOpenHom V₂ ≫ ψ.left.unop
  have hb : (CrystallineThickening.ι S).op.map (P.restrictOpenHom V₂).op ≫ σ'.op =
      b ≫ (B.restrictOpenLE h).op := Quiver.Hom.unop_inj hσ'
  have hk : (CrystallineThickening.ι S).op.map k.op ≫ σ'.op = tauIdx τ W' :=
    map_restrictOpenHom_comp_op_comp_eq_tauIdx τ h V₂ _ σ' hσ' ψ.left.unop
      (congrArg Quiver.Hom.unop (CostructuredArrow.w ψ))
  let R₁ := (tauRestrict F τ h).hom.toAddMonoidHom
  let R₂ : diagramObj (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
      (CostructuredArrow.mk b) →+ _ :=
    (baseChangeMap ((crisCommRing S).map b).hom
      ((crisCommRing S).map (b ≫ (B.restrictOpenLE h).op)).hom
      (σ := ((crisCommRing S).map (B.restrictOpenLE h).op).hom) (ρ := RingHom.id _)
      (fun a ↦ by rw [Functor.map_comp]; rfl) LinearMap.id).hom.toAddMonoidHom
  let D := (diagramMap (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
    (transitionHom k (tauIdx τ W') σ'.op hk)).hom.toAddMonoidHom
  let J := (diagramMap (CrystallineThickening.ι S) (crisCommRing S) (ulModel F)
    (CostructuredArrow.homMk (f := CostructuredArrow.mk (b ≫ (B.restrictOpenLE h).op))
      (f' := CostructuredArrow.mk σ'.op) (P.restrictOpenHom V₂).op hb)).hom.toAddMonoidHom
  let Ψ :=
    (diagramMap (CrystallineThickening.ι S) (crisCommRing S) (ulModel F) ψ).hom.toAddMonoidHom
  have hcomm : ∀ z, D (R₁ z) = J (R₂ (Ψ z)) := fun z ↦ by
    induction z using TensorProduct.inductionOn with
    | tmul r m =>
        change tmul _ (((crisCommRing S).map (B.restrictOpenLE h).op).hom r)
            ((ulModel F).restrictₛₗ k.op m) =
          tmul _ (((crisCommRing S).map (B.restrictOpenLE h).op).hom r)
            ((ulModel F).restrictₛₗ (P.restrictOpenHom V₂).op
              ((ulModel F).restrictₛₗ ψ.left m))
        rw [← PresheafOfModules.restrictₛₗ_comp_apply]
        rfl
    | add z z' hz hz' =>
        exact (map_add (D.comp R₁) z z').trans ((congrArg₂ (· + ·) hz hz').trans
          (map_add (J.comp (R₂.comp Ψ)) z z').symm)
  refine ⟨W', h, hpW', (bijective_diagramMap_transitionHom F k _ σ'.op hk hF hcrys).1 ?_⟩
  change D (R₁ y) = D 0
  rw [hcomm, show Ψ y = 0 from hψ, map_zero, map_zero]
  exact map_zero J

end Local

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
