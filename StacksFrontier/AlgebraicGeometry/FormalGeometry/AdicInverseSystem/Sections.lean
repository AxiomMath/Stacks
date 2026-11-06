module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Affine sections of an adic inverse system

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf and `U ⊆ X` an affine open. This file
computes the modules of sections over `U` of the objects attached to `I` in
`Stacks.Algebraization`: the subsheaf `I ^ n M` has `I(U) ^ n • M(U)` as its sections when `M` is
quasi-coherent, and consequently each transition map of an adic inverse system presents `F_n(U)`
as the quotient `F_{n+1}(U) / I(U) ^ (n+1) F_{n+1}(U)`.

Both statements are proved by transporting to `Spec Γ(X, U)`, where a quasi-coherent module is
`M̃` for an honest module and the global-sections functor is an equivalence. The transport is
`affineSectionsEquiv`, the semilinear identification of `Γ(M|_U, ⊤)` with `Γ(M, U)`.

## Main definitions

* `Stacks.Algebraization.affineSectionsEquiv` — the sections of `M` over an affine open `U` as a
  `Γ(X, U)`-module, identified with the global sections of the restriction of `M` to
  `Spec Γ(X, U)`.

## Main results

* `Stacks.Algebraization.submodule_le_of_affine` and `submodule_eq_of_iso` — comparison of
  submodules of a sheaf of modules is affine-local, and two submodules carrying an isomorphism
  over the ambient sheaf are equal.
* `Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen` — an epimorphism of quasi-coherent
  modules is surjective on sections over an affine open.
* `Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine` — the sections of `I ^ n M`
  over an affine open `U` are exactly `I(U) ^ n • M(U)`.
* `Stacks.Algebraization.AdicInverseSystem.sectionsQuotientEquiv` — each transition of an adic
  inverse system is, on the sections over an affine open, the canonical quotient by the
  corresponding power of the ideal.

## Implementation notes

The inclusion `I(U) ^ n • M(U) ≤ Γ(I ^ n M, U)` is the defining property of `I ^ n M` and needs
nothing. The reverse inclusion is where quasi-coherence enters: `I ^ n M` is an infimum, so to
bound it above by the sectionwise multiple one must exhibit the sectionwise multiple as the
sections of an actual subsheaf, and that subsheaf is produced as the kernel of the map to the
pushforward of `M̃|_U / I(U) ^ n M̃|_U` from `Spec Γ(X, U)`. `pushforward_annihilated` is the
statement that this pushforward is annihilated by `I ^ n` over every affine open, which is what
makes `I ^ n M` land in the kernel.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared category instances; composites that mix them are written
with `(C := X.Modules)` supplied at the call site, and the scalar action on sections is supplied by
the `local instance`s below, each of which is an existing instance restated at the spelling the
elaborator meets.

## References

* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### Bridging instances for the scalar action on sections

The module structure on sections is declared over `X.ringCatSheaf.obj.obj U` in
`Mathlib.Algebra.Category.ModuleCat.Sheaf` and over `Γ(X, U)` in
`Mathlib.AlgebraicGeometry.Modules.Sheaf`, and instance search cannot cross the `TopCat.Sheaf`
definition to see that the two agree. The bridging instances are stated once in
`Completion.IdealPowerQuasicoherent` and re-enabled here. -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf
  sectionsModuleRingCatSheaf monoSubmoduleι

/-- The sections of a module over an affine open `U`, identified with the global sections of its
restriction along `Spec Γ(X, U) ⟶ X`, semilinearly over `Γ(X, U)`.

Additively this is `SheafOfModules.restrictAppIso` followed by the identification of `U` with the
image of the whole of `Spec Γ(X, U)`; the content is that the composite is `Γ(X, U)`-linear, which
comes down to the structure map of `Spec Γ(X, U)` inverting `Scheme.ΓSpecIso`. -/
public noncomputable def affineSectionsEquiv {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Γ(M.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  let f := hU.fromSpec
  have hImage : U = f ''ᵁ ⊤ := by rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let eTopAb : Γ(M.restrict f, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso f ⊤ ≪≫ M.presheaf.mapIso (eqToIso hImage).op
  let eTop0 : Γ(M.restrict f, ⊤) ≃+ Γ(M, U) := eTopAb.addCommGroupIsoToAddEquiv
  let eRing : Γ(X, f ''ᵁ ⊤) ≅ Γ(X, U) := X.presheaf.mapIso (eqToIso hImage).op
  have hR (a : Γ(X, U)) :
      eRing.hom ((f.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv a)) = a := by
    have hAEq : eRing.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv = (f.appIso ⊤).hom := by
      simp only [eRing, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appIso_hom']
      have hAppLE : hU.fromSpec.appLE U ⊤ (by simp) = (Scheme.ΓSpecIso Γ(X, U)).inv := by
        simp only [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
          ← Functor.map_comp]
        simp
      rw [← hAppLE]
      have hpre : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ (hU.fromSpec ''ᵁ ⊤) := by
        intro x hx
        exact ⟨x, trivial, rfl⟩
      simpa only [eqToIso.hom] using (hU.fromSpec.map_appLE'
        (U := hU.fromSpec ''ᵁ ⊤) (U' := U)
        (V := (⊤ : (Spec Γ(X, U)).Opens)) hpre hImage)
    have hAEq' : eRing.hom = (f.appIso ⊤).hom ≫ (Scheme.ΓSpecIso Γ(X, U)).hom := by
      rw [← hAEq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [hAEq', ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  have htop (a : Γ(X, U)) (m' : Γ(M.restrict f, ⊤)) :
      eTop0 (a • m') = a • eTop0 m' := by
    change eTopAb.hom (a • m') = a • eTopAb.hom m'
    rw [Scheme.Modules.smul_Spec_def]
    have hres : (Spec Γ(X, U)).presheaf.map (⊤ : (Spec Γ(X, U)).Opens).leTop.op = 𝟙 _ := rfl
    rw [hres]
    simp only [CategoryTheory.id_apply]
    simp only [eTopAb, Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [Functor.mapIso_hom, Iso.op_hom] at *
    rw [M.map_smul]
    congr 1
    exact hR a
  exact
    show Γ(M.restrict f, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) from { eTop0 with map_smul' := htop }

/-- Comparison of two submodules of a sheaf of modules is affine-local. -/
public lemma submodule_le_of_affine {X : Scheme.{u}} {M : X.Modules}
    (P Q : M.Submodule)
    (h : ∀ U : X.affineOpens,
      P.toSubmodule.obj (op U.1) ≤ Q.toSubmodule.obj (op U.1)) : P ≤ Q := by
  refine SheafOfModules.Submodule.le_iff.mpr (PresheafOfModules.Submodule.le_iff.mpr ?_)
  intro U s hs
  exact mem_submodule_of_affine Q U.unop s fun V i => h V (P.toSubmodule.map i.op hs)

/-- Two submodules of a sheaf of modules carrying an isomorphism compatible with their inclusions
into the ambient sheaf are equal. -/
public lemma submodule_eq_of_iso {X : Scheme.{u}} {M : X.Modules}
    (P Q : M.Submodule) (e : P.toSheafOfModules ≅ Q.toSheafOfModules)
    (hcomp : e.hom ≫ Q.ι = P.ι) : P = Q := by
  have key : ∀ (R S : M.Submodule) (d : R.toSheafOfModules ≅ S.toSheafOfModules),
      d.hom ≫ S.ι = R.ι → R ≤ S := by
    intro R S d hd
    refine submodule_le_of_affine R S fun U x hx => ?_
    have hz : ((d.hom.val.app (op U.1)).hom ⟨x, hx⟩).val = x :=
      congrArg (fun k : R.toSheafOfModules ⟶ M => (k.val.app (op U.1)).hom ⟨x, hx⟩) hd
    exact hz ▸ ((d.hom.val.app (op U.1)).hom ⟨x, hx⟩).property
  exact le_antisymm (key P Q e hcomp) (key Q P e.symm (e.inv_comp_eq.mpr hcomp.symm))

/-- An epimorphism of quasi-coherent modules is surjective on the sections over an affine open.

On `Spec Γ(X, U)` a quasi-coherent module is `M̃`, and `M ↦ Γ(M, ⊤)` is an equivalence onto
modules, so an epimorphism there is a surjection of modules. -/
public lemma surjective_app_of_epi_of_isAffineOpen {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (U : X.affineOpens) :
    Function.Surjective (f.app U.1) := by
  let g := U.2.fromSpec
  have : IsOpenImmersion g := U.2.isOpenImmersion_fromSpec
  let f' := (Scheme.Modules.restrictFunctor g).map f
  let P := SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of Γ(X, U))).ringCatSheaf
  let M' : P.FullSubcategory := ⟨M.restrict g, by infer_instance⟩
  let N' : P.FullSubcategory := ⟨N.restrict g, by infer_instance⟩
  let f'' : M' ⟶ N' := ObjectProperty.homMk f'
  have hf'' : Epi f'' := by
    constructor
    intro Z a b hab
    apply ObjectProperty.hom_ext _
    exact (cancel_epi f').mp (congrArg (fun k => k.hom) hab)
  let E := AlgebraicGeometry.tildeEquiv (R := CommRingCat.of Γ(X, U))
  have hEpiΓ : Epi (E.inverse.map f'') := Functor.map_epi E.inverse f''
  have hs : Function.Surjective (f'.app ⊤) := by
    have h := (ModuleCat.epi_iff_surjective _).mp hEpiΓ
    change Function.Surjective (f'.app ⊤) at h
    exact h
  have hnat : f'.app ⊤ ≫ (N.restrictAppIso g ⊤).hom =
      (M.restrictAppIso g ⊤).hom ≫ f.app (g ''ᵁ ⊤) := by
    ext x
    rfl
  have hU : g ''ᵁ ⊤ = U.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  rw [← hU]
  intro y
  obtain ⟨x, hx⟩ := hs ((N.restrictAppIso g ⊤).inv y)
  refine ⟨(M.restrictAppIso g ⊤).hom x, ?_⟩
  have h := congrArg (fun k => k x) hnat
  change (N.restrictAppIso g ⊤).hom (f'.app ⊤ x) =
      f.app (g ''ᵁ ⊤) ((M.restrictAppIso g ⊤).hom x) at h
  rw [← h, hx]
  simp

/-- Evaluation of `modulesSpecToSheaf` on a morphism is the morphism's own action on sections. -/
private lemma modulesSpecToSheaf_map_apply {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (g : M ⟶ N) (W : (Spec R).Opens) (x : Γ(M, W)) :
    ((modulesSpecToSheaf.map g).hom.app (op W)) x = g.app W x := rfl

/-- The global-sections functor on an affine spectrum, applied to a morphism and an element, is
the morphism's own action on global sections. -/
private lemma moduleSpecΓFunctor_map_apply {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (g : M ⟶ N) (x : Γ(M, ⊤)) :
    (moduleSpecΓFunctor (R := R)).map g x = g.app ⊤ x := rfl

/-- A scalar annihilating the global sections of a quasi-coherent module on an affine scheme
annihilates its sections over every open.

Multiplication by the scalar is a morphism of modules, so it is determined by its effect on
global sections, which is where quasi-coherence is used. -/
private lemma smul_eq_zero_of_forall_top {R : CommRingCat.{u}}
    (T : (Spec R).Modules) [T.IsQuasicoherent] (r : R)
    (h : ∀ x : Γ(T, ⊤), r • x = 0) (V : (Spec R).Opens) (x : Γ(T, V)) :
    r • x = 0 := by
  let a' : modulesSpecToSheaf.obj T ⟶ modulesSpecToSheaf.obj T :=
    ⟨{ app := fun W => ConcreteCategory.ofHom (C := ModuleCat R)
         (X := (modulesSpecToSheaf.obj T).obj.obj W)
         (Y := (modulesSpecToSheaf.obj T).obj.obj W)
         (LinearMap.lsmul R Γ(T, W.unop) r)
       naturality := by
         intro W Z i
         ext y
         exact (((modulesSpecToSheaf.obj T).obj.map i).hom.map_smul r y).symm }⟩
  let a : T ⟶ T := SpecModulesToSheafFullyFaithful.preimage a'
  have haapp (W : (Spec R).Opens) (x : Γ(T, W)) : a.app W x = r • x := by
    have hh := congrArg (fun k => (k.hom.app (op W)) x)
      (SpecModulesToSheafFullyFaithful.map_preimage a')
    simp only [modulesSpecToSheaf_map_apply, a'] at hh
    convert hh using 1
    rfl
  let T' : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨T, inferInstance⟩
  have ha : a = 0 := by
    have he : (tildeEquiv (R := R)).inverse.map (ObjectProperty.homMk a : T' ⟶ T') =
        (tildeEquiv (R := R)).inverse.map (ObjectProperty.homMk 0 : T' ⟶ T') := by
      apply ModuleCat.hom_ext
      ext y
      show (a.app ⊤).hom y = ((0 : T ⟶ T).app ⊤).hom y
      have h0 : ((0 : T ⟶ T).app ⊤) y = 0 := rfl
      exact ((haapp ⊤ y).trans (h y)).trans h0.symm
    exact congrArg (fun k => k.hom) ((tildeEquiv (R := R)).inverse.map_injective he)
  have hh := congrArg (fun k => (k.app V).hom x) ha
  simpa only [haapp, Scheme.Modules.Hom.zero_app, AddCommGrpCat.zero_apply] using hh

/-- Restricting a section of the structure sheaf and then pulling it back along `fromSpec` is
pulling it back and then restricting. -/
private lemma fromSpec_map_app {X : Scheme.{u}} (U : X.affineOpens)
    {W : X.Opens} (hWU : W ≤ U.1) (r : Γ(X, U)) :
    (U.2.fromSpec.app W) (X.presheaf.map (homOfLE hWU).op r) =
      (Spec Γ(X, U)).presheaf.map (U.2.fromSpec ⁻¹ᵁ W).leTop.op
        ((Scheme.ΓSpecIso Γ(X, U)).inv r) := by
  have h := U.2.fromSpec.naturality (homOfLE hWU).op
  rw [U.2.fromSpec_app_self] at h
  have hh := congrArg (fun k => k r) h
  simp only [Category.assoc, ← Functor.map_comp, ConcreteCategory.comp_apply] at hh
  convert hh using 2

/-- The pushforward along `Spec Γ(X, U) ⟶ X` of a module annihilated by an ideal of `Γ(X, U)` is
annihilated by that ideal over every affine open of `X`.

The statement is local, and over an affine open contained in `U` the ideal of sections of `I` is
generated by the restrictions from `U`, which is `Scheme.IdealSheafData.map_ideal`. -/
private lemma pushforward_annihilated {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (T : (Spec Γ(X, U)).Modules) [T.IsQuasicoherent]
    (hT : ∀ r ∈ I.ideal U, ∀ x : Γ(T, ⊤), r • x = 0)
    (V : X.affineOpens) (r : Γ(X, V)) (hr : r ∈ I.ideal V)
    (x : Γ((Scheme.Modules.pushforward U.2.fromSpec).obj T, V)) : r • x = 0 := by
  let f := U.2.fromSpec
  have hfi : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let H := (Scheme.Modules.pushforward f).obj T
  have hsmall (W : X.affineOpens) (hWU : W ≤ U) (s : Γ(X, W))
      (hs : s ∈ I.ideal W) (y : Γ(H, W)) : s • y = 0 := by
    rw [← I.map_ideal hWU] at hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨a, ha, rfl⟩ := hs
      change Γ(T, f ⁻¹ᵁ W.1) at y
      show (f.app W.1) (X.presheaf.map (homOfLE hWU).op a) • y = 0
      dsimp only [f] at y ⊢
      exact (congrArg (fun b : Γ(Spec Γ(X, U), f ⁻¹ᵁ W.1) => b • y)
        (fromSpec_map_app U hWU a)).trans
        (smul_eq_zero_of_forall_top T a (hT a ha) (f ⁻¹ᵁ W.1) y)
    | zero => exact zero_smul _ _
    | add a b ha hb h₁ h₂ => rw [add_smul, h₁, h₂, add_zero]
    | smul a b hb h => rw [smul_eq_mul, mul_smul, h, smul_zero]
  show @SMul.smul Γ(Spec Γ(X, U), f ⁻¹ᵁ V.1) Γ(T, f ⁻¹ᵁ V.1) inferInstance
    (f.app V.1 r) x = 0
  apply TopCat.Presheaf.IsSheaf.section_ext T.isSheaf
  intro z hz
  have hzU : f z ∈ U.1 := by
    have : f z ∈ f.opensRange := ⟨z, rfl⟩
    simpa only [f, U.2.opensRange_fromSpec] using this
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show f z ∈ V.1 ⊓ U.1 from ⟨hz, hzU⟩)
      (V.1 ⊓ U.1).2
  let W' : X.affineOpens := ⟨W, hW⟩
  have hWV' : W ≤ V.1 := le_trans hWV inf_le_left
  have hWU : W ≤ U.1 := le_trans hWV inf_le_right
  refine ⟨f ⁻¹ᵁ W, (Opens.map f.base).monotone hWV', hzW, ?_⟩
  show H.presheaf.map (homOfLE hWV').op (r • x) =
    H.presheaf.map (homOfLE hWV').op 0
  rw [H.map_smul, map_zero]
  exact hsmall W' hWU (X.presheaf.map (homOfLE hWV').op r)
    (I.ideal_le_comap_ideal hWV' hr) _

/-- `affineSectionsEquiv` is natural in the module: restricting a morphism to `Spec Γ(X, U)`
and reading it on global sections is the morphism's own action on the sections over `U`. -/
lemma affineSectionsEquiv_naturality {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N)
    (U : X.Opens) (hU : IsAffineOpen U) [IsOpenImmersion hU.fromSpec]
    (x : Γ(M.restrict hU.fromSpec, ⊤)) :
    affineSectionsEquiv N U hU (((Scheme.Modules.restrictFunctor hU.fromSpec).map g).app ⊤ x) =
      g.app U (affineSectionsEquiv M U hU x) := by
  let i : op (hU.fromSpec ''ᵁ ⊤) ⟶ op U :=
    (eqToHom (show U = hU.fromSpec ''ᵁ ⊤ by
      rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])).op
  show N.presheaf.map i (g.app _ x) = g.app _ (M.presheaf.map i x)
  exact (congrArg (fun k => k x) (g.mapPresheaf.naturality i)).symm

/-- The sections of `I ^ n M` over an affine open `U` are exactly `I(U) ^ n • M(U)`, for `M`
quasi-coherent.

One inclusion is the defining property of `I ^ n M`. For the other, transport to `Spec Γ(X, U)`,
form the honest quotient `M(U) / I(U) ^ n M(U)` there, and observe that `I ^ n M` lands in the
kernel of the resulting map out of `M`, because the pushforward of that quotient is annihilated
by `I ^ n` on every affine open. -/
public lemma idealPowerMultiple_toSubmodule_obj_affine {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] (U : X.affineOpens) :
    (idealPowerMultiple I n M).toSubmodule.obj (op U.1) =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) := by
  let P := idealPowerMultiple I n M
  apply le_antisymm
  swap
  · exact (idealPowerMultiple_le_iff I n M P).mp le_rfl U
  let f := U.2.fromSpec
  have hfi : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let R : CommRingCat.{u} := Γ(X, U.1)
  let L := tilde.functor R
  let G := moduleSpecΓFunctor (R := R)
  let adjT := tilde.adjunction (R := R)
  let F := M.restrict f
  have hFq : F.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor f M
  let A : ModuleCat R := G.obj F
  let K : Submodule R A := (I ^ n).ideal U • ⊤
  let B : ModuleCat R := ModuleCat.of R (A ⧸ K)
  let T := L.obj B
  let p : A ⟶ B := ConcreteCategory.ofHom (C := ModuleCat R) (X := A) (Y := B) K.mkQ
  have hFiso : IsIso F.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  have hciso : IsIso (adjT.counit.app F) := hFiso
  let e := asIso (adjT.counit.app F)
  let q : F ⟶ T := e.inv ≫ L.map p
  have htri : adjT.unit.app A ≫ G.map e.hom = 𝟙 A := adjT.right_triangle_components F
  have he' : G.map e.inv = adjT.unit.app A := by
    refine (cancel_mono (G.map e.hom)).1 ?_
    rw [← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    exact htri.symm
  have hq : G.map q = p ≫ adjT.unit.app B :=
    (Functor.map_comp _ _ _).trans
      ((congrArg (fun g => g ≫ G.map (L.map p)) he').trans (adjT.unit.naturality p).symm)
  have huiso : IsIso (adjT.unit.app B) := inferInstanceAs (IsIso (tilde.toOpen B ⊤))
  have hT : ∀ r ∈ (I ^ n).ideal U, ∀ x : Γ(T, ⊤), r • x = 0 := by
    intro r hr x
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (adjT.unit.app B)).mp inferInstance x
    show r • (adjT.unit.app B).hom y = (0 : G.obj T)
    rw [← (adjT.unit.app B).hom.map_smul]
    have hy : r • y = (0 : B) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective K y
      apply (Submodule.Quotient.mk_eq_zero K).mpr
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    rw [hy, map_zero]
  let adj := Scheme.Modules.restrictAdjunction f
  let q' : M ⟶ (Scheme.Modules.pushforward f).obj T := (adj.homEquiv M T) q
  let P' : X.Modules := P.toSheafOfModules
  let Pι : P' ⟶ M := P.ι
  let Q := kernelSubmodule q'
  have hvanish : ∀ V : X.affineOpens, ∀ z : Γ(M, V.1),
      z ∈ I.ideal V ^ n • (⊤ : Submodule Γ(X, V.1) Γ(M, V.1)) →
      q'.app V.1 z = 0 := by
    intro V z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro r hr w _
      rw [Scheme.Modules.Hom.app_smul]
      exact pushforward_annihilated (I ^ n) U T hT V r hr _
    · intro w w' hw hw'
      rw [map_add, hw, hw', add_zero]
  have hPQ : P ≤ Q := by
    apply (idealPowerMultiple_le_iff I n M Q).mpr
    intro V x hx
    rw [kernelSubmodule_toSubmodule_obj]
    exact hvanish V x hx
  have hz : Pι ≫ q' = 0 := by
    refine Scheme.Modules.hom_ext _ _ fun V => ?_
    ext x
    have hx : x.1 ∈ (kernelSubmodule q').toSubmodule.obj (op V) := hPQ (op V) x.property
    rw [kernelSubmodule_toSubmodule_obj] at hx
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app]
    exact hx
  have hzq : (Scheme.Modules.restrictFunctor f).map Pι ≫ q = 0 := by
    refine (adj.homEquiv P' T).injective ?_
    have h1 : (adj.homEquiv P' T) ((Scheme.Modules.restrictFunctor f).map Pι ≫ q)
        = Pι ≫ q' := adj.homEquiv_naturality_left Pι q
    rw [h1, hz, Adjunction.homEquiv_unit]
    simp
  intro x hx
  let z : Γ(P', U) := ⟨x, hx⟩
  let z' := (affineSectionsEquiv P' U.1 U.2).symm z
  let y : A := ((Scheme.Modules.restrictFunctor f).map Pι).app ⊤ z'
  have hy : K.mkQ y = 0 := by
    apply (ModuleCat.mono_iff_injective (adjT.unit.app B)).mp inferInstance
    rw [map_zero]
    have hqy : (ConcreteCategory.hom (G.map q)) y = (adjT.unit.app B) (K.mkQ y) :=
      congrArg (fun k : A ⟶ G.obj T => (ConcreteCategory.hom k) y) hq
    have h0 : q.app ⊤ y = 0 := by
      have h := congrArg (fun k => k.app ⊤ z') hzq
      simpa using h
    exact hqy.symm.trans ((moduleSpecΓFunctor_map_apply q y).trans h0)
  have hyK : y ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hy
  have heval : affineSectionsEquiv M U.1 U.2 y = x := by
    rw [affineSectionsEquiv_naturality (U := U.1) (hU := U.2)]
    simp only [z']
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [← heval]
  exact Submodule.smul_top_le_comap_smul_top ((I ^ n).ideal U)
    (affineSectionsEquiv M U.1 U.2).toLinearMap hyK

namespace AdicInverseSystem

/-- Each transition of an adic inverse system is, on the sections over an affine open, the
canonical quotient by the corresponding power of the ideal.

The transition `F_{n+1} ⟶ F_n` is by hypothesis the cokernel projection of
`I ^ (n+1) F_{n+1} ⟶ F_{n+1}` followed by an isomorphism, and the inclusion of a submodule is a
monomorphism, so in the abelian category of modules it is also the *kernel* of that cokernel
projection, hence of the transition. Over an affine open the sections of
`I ^ (n+1) F_{n+1}` are `I(U) ^ (n+1) F_{n+1}(U)` by
`idealPowerMultiple_toSubmodule_obj_affine`, and the transition is surjective on affine sections
by `surjective_app_of_epi_of_isAffineOpen`. -/
public lemma sectionsQuotientEquiv (S : AdicInverseSystem.{u}) (U : S.X.affineOpens)
    (n : ℕ) :
    ∃ e : (Γ(S.system.obj (op (n + 1)), U) ⧸
          (S.I.ideal U ^ (n + 1) •
            (⊤ : Submodule Γ(S.X, U) Γ(S.system.obj (op (n + 1)), U)))) ≃ₗ[Γ(S.X, U)]
        Γ(S.system.obj (op n), U),
      ∀ x, e (Submodule.Quotient.mk x) =
        ((S.system.map (homOfLE (Nat.le_succ n)).op).app U.1).hom x := by
  let M := S.system.obj (op (n + 1))
  let N := S.system.obj (op n)
  let P := idealPowerMultiple S.I (n + 1) M
  let P' : S.X.Modules := P.toSheafOfModules
  let Pι : P' ⟶ M := P.ι
  let t : M ⟶ N := S.system.map (homOfLE (Nat.le_succ n)).op
  let Q : M.Submodule := kernelSubmodule t
  have ht : cokernel.π (C := S.X.Modules) Pι ≫ (S.quotientIso n).hom = t :=
    S.quotientIso_hom_comp n
  have hcokerKer : IsLimit (KernelFork.ofι (f := cokernel.π (C := S.X.Modules) Pι) Pι
      (cokernel.condition (C := S.X.Modules) Pι)) :=
    Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π (C := S.X.Modules) Pι)
        (cokernel.condition (C := S.X.Modules) Pι))
      (cokernelIsCokernel (C := S.X.Modules) Pι)
  have hiff : ∀ ⦃W : S.X.Modules⦄ (φ : W ⟶ M),
      φ ≫ cokernel.π (C := S.X.Modules) Pι = 0 ↔ φ ≫ t = 0 := by
    intro W φ
    rw [← ht, ← Category.assoc,
      Preadditive.IsIso.comp_right_eq_zero (g := (S.quotientIso n).hom)]
  have hzero : Pι ≫ t = 0 := (hiff Pι).mp (cokernel.condition _)
  have hkerP : IsLimit (KernelFork.ofι (f := t) Pι hzero) :=
    KernelFork.isLimitOfIsLimitOfIff' hcokerKer t hiff
  let eP : P' ≅ kernel (C := S.X.Modules) t :=
    IsLimit.conePointUniqueUpToIso hkerP (limit.isLimit (parallelPair t 0))
  have heP : eP.hom ≫ kernel.ι (C := S.X.Modules) t = Pι :=
    IsLimit.conePointUniqueUpToIso_hom_comp hkerP (limit.isLimit (parallelPair t 0))
      WalkingParallelPair.zero
  let eQ := kernelSubmoduleIso t
  have heQi : eQ.inv ≫ Q.ι = kernel.ι (C := S.X.Modules) t :=
    kernelSubmoduleCorestrict_comp_ι t
  let ePQ : P' ≅ (Q.toSheafOfModules : S.X.Modules) := eP.trans eQ.symm
  have hPQ : ePQ.hom ≫ Q.ι = Pι :=
    (Category.assoc _ _ _).trans ((congrArg (fun g => eP.hom ≫ g) heQi).trans heP)
  have hsub : P = Q := submodule_eq_of_iso P Q ePQ hPQ
  have hMq : M.IsQuasicoherent := S.isQuasicoherent (op (n + 1))
  let tU : Γ(M, U.1) →ₗ[Γ(S.X, U.1)] Γ(N, U.1) := (t.val.app (op U.1)).hom
  have hsurj : Function.Surjective tU := by
    have hepi : Epi (C := S.X.Modules) t :=
      ht ▸ (inferInstance :
        Epi (C := S.X.Modules) (cokernel.π (C := S.X.Modules) Pι ≫ (S.quotientIso n).hom))
    have hNq : N.IsQuasicoherent := S.isQuasicoherent (op n)
    exact surjective_app_of_epi_of_isAffineOpen t U
  let J := S.I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(S.X, U.1) Γ(M, U.1))
  have hkerPsec : LinearMap.ker tU = P.toSubmodule.obj (op U.1) := by
    rw [hsub]
    exact (kernelSubmodule_toSubmodule_obj t (op U.1)).symm
  have hker : LinearMap.ker tU = J := by
    rw [hkerPsec]
    exact idealPowerMultiple_toSubmodule_obj_affine S.I (n + 1) M U
  let e : (Γ(M, U.1) ⧸ J) →ₗ[Γ(S.X, U.1)] Γ(N, U.1) := J.liftQ tU (by
    intro x hx
    apply LinearMap.mem_ker.mp
    rw [hker]
    exact hx)
  have heinj : Function.Injective e := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective J b
    apply (Submodule.Quotient.eq J).2
    rw [← hker]
    apply LinearMap.mem_ker.mpr
    have hab' : tU x = tU y := hab
    rw [map_sub, hab']
    simp
  have hesurj : Function.Surjective e := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    exact hx
  exact ⟨LinearEquiv.ofBijective e ⟨heinj, hesurj⟩, fun _ => rfl⟩

end AdicInverseSystem

end Stacks.Algebraization

end

end
