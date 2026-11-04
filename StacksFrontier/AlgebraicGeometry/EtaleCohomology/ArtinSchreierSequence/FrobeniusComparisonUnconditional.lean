module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparison
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparison

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheafCohomology
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusSurjectivity
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ScalarAction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Artin–Schreier map on the étale cohomology of `𝐆_a`

Let `X` be a scheme over a field `k`. The cohomology `Hᵈ(X, 𝒪_X)` is additively isomorphic to
`Hᵈ(X_étale, 𝐆_a)`, by an isomorphism carrying the action of `a ∈ k` to `Hᵈ` of multiplication by
the image of `a` in `Γ(X, 𝒪_X)`. When `k` is algebraically closed of characteristic `p > 0` and
`Hᵈ(X, 𝒪_X)` is finite-dimensional, the Artin–Schreier map `F - 1` is surjective on
`Hᵈ(X_étale, 𝐆_a)`.

## Main definitions

* `Stacks.ArtinSchreier.scalarMap`: multiplication by a global function on `𝐆_a`.
* `Stacks.ArtinSchreier.cohomologyOverFieldAddEquivSheafH`: the isomorphism of `Hⁿ⁺¹(X, 𝒪_X)`
  with `Hⁿ⁺¹(X_étale, 𝐆_a)`.
* `Stacks.ArtinSchreier.cohomologyOverFieldZeroAddEquivSheafH`: the isomorphism of `H⁰(X, 𝒪_X)`
  with `H⁰(X_étale, 𝐆_a)`.

## Main results

* `Stacks.ArtinSchreier.exists_addEquiv_cohomologyOverField_sheafH`: in every degree `d`, an
  additive isomorphism of `Hᵈ(X, 𝒪_X)` with `Hᵈ(X_étale, 𝐆_a)` carrying the `k`-action to
  multiplication by global functions.
* `Stacks.ArtinSchreier.surjective_sheafH_map_artinSchreierMap`: `F - 1` is surjective on
  `Hᵈ(X_étale, 𝐆_a)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open AlgebraicGeometry

universe u v w

namespace CategoryTheory.Sheaf

/-- `H ^ n` is additive in the morphism: the difference of two morphisms induces the difference
of the induced maps. -/
theorem H.map_sub_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{v} (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (f g : F ⟶ G) (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map (f - g) n x = Sheaf.H.map f n x - Sheaf.H.map g n x := by
  rw [eq_sub_iff_add_eq, ← Sheaf.H.map_add_apply, sub_add_cancel]

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

/-- **Pulling a section of the structure sheaf back is semilinear**, read in the structure sheaf
upstairs: for `g : Y ⟶ Z`, `r ∈ Γ(Z, U)` and a section `s` of `𝒪_Z` over `U`, identifying the
pullback of `r • s` with a function on `W` by `pullbackUnitIso` gives `g^♯ r` times the function
attached to `s`. -/
theorem pullbackUnitIso_hom_app_pullbackSectionHom_smul {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (U : Z.Opens) (W : Y.Opens) (h : W ≤ g ⁻¹ᵁ U) (r : Γ(Z, U))
    (s : Γ(Scheme.unitModule Z, U)) :
    (Scheme.Modules.pullbackUnitIso g).hom.app W
        (pullbackSectionHom g (Scheme.unitModule Z) U W h (r • s)) =
      g.appLE U W h r •
        (Scheme.Modules.pullbackUnitIso g).hom.app W
          (pullbackSectionHom g (Scheme.unitModule Z) U W h s) := by
  rw [pullbackSectionHom_smul, Scheme.Modules.Hom.app_smul]

end AlgebraicGeometry

namespace Stacks.ArtinSchreier

/-- **Transport of the surjectivity of `F - 1` along an additive equivalence.** Let `W` be a
finite-dimensional vector space over an algebraically closed field `k` of characteristic `p > 0`
and `E : W ≃+ V` an additive bijection carrying the scalar `a` to an additive endomorphism `S a`
of `V`. If `Φ` is an additive endomorphism of `V` with `Φ ∘ S a = S (a ^ p) ∘ Φ`, then `Φ - 1` is
surjective. -/
theorem surjective_sub_self_of_addEquiv {p : ℕ} (hp : 0 < p) (k : Type*) [Field k]
    [IsAlgClosed k] [CharP k p] {W V : Type*} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [AddCommGroup V] (E : W ≃+ V) (Φ : V →+ V) (S : k → V →+ V)
    (hE : ∀ (a : k) (w : W), E (a • w) = S a (E w))
    (hΦ : ∀ (a : k) (v : V), Φ (S a v) = S (a ^ p) (Φ v)) :
    Function.Surjective fun v ↦ Φ v - v := by
  let F : W →+ W := E.symm.toAddMonoidHom.comp (Φ.comp E.toAddMonoidHom)
  have hF : ∀ (a : k) (w : W), F (a • w) = a ^ p • F w := by
    intro a w
    apply E.injective
    simp [F, hE, hΦ]
  intro y
  obtain ⟨w, hw⟩ := frobeniusSemilinear_sub_id_surjective k hp W F hF (E.symm y)
  refine ⟨E w, E.symm.injective ?_⟩
  simpa [F] using hw

variable (X : Scheme.{u})

/-- Pulling back along a morphism of étale `X`-schemes is compatible with multiplication by the
pullback of a global function on `X`. -/
theorem appTop_mul_appTop {U V : X.Etale} (f : V ⟶ U) (c : Γ(X, ⊤)) (x : Γ(U.left, ⊤)) :
    f.left.appTop (U.hom.appTop (X := U.left) c * x) =
      V.hom.appTop (X := V.left) c * f.left.appTop x := by
  rw [map_mul, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    MorphismProperty.Over.w f]

/-- **Multiplication by a global function on `𝐆_a`.** For `c ∈ Γ(X, 𝒪_X)`, the endomorphism of
the additive group of the small étale site of `X` which multiplies a section over `U` by the
pullback of `c` to `U`. -/
def scalarMap (c : Γ(X, ⊤)) : additiveSheaf.{u, v} X ⟶ additiveSheaf.{u, v} X :=
  ⟨{ app U := AddCommGrpCat.uliftFunctor.map
        (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft (R := Γ(U.unop.left, ⊤))
          (U.unop.hom.appTop c)))
     naturality _ _ f :=
       AddCommGrpCat.ext fun ⟨x⟩ ↦ congrArg ULift.up (appTop_mul_appTop X f.unop c x).symm }⟩

/-- Multiplication by `c` on `𝐆_a` multiplies each section by the pullback of `c`. -/
@[simp]
theorem scalarMap_app_ofSection (c : Γ(X, ⊤)) (U : X.Etale) (x : Γ(U.left, ⊤)) :
    (scalarMap.{u, v} X c).hom.app (op U) (ofSection x) =
      ofSection (U.hom.appTop (X := U.left) c * x) :=
  rfl

/-- **Frobenius is semilinear for the multiplication by global functions**: `(c x) ^ p =
c ^ p x ^ p`. -/
theorem scalarMap_comp_frobeniusMap {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (c : Γ(X, ⊤)) :
    scalarMap.{u, v} X c ≫ frobeniusMap.{u, v} X hp hX =
      frobeniusMap.{u, v} X hp hX ≫ scalarMap.{u, v} X (c ^ p) := by
  ext U x
  obtain ⟨x, rfl⟩ := ofSection_surjective x
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  rw [scalarMap_app_ofSection, frobeniusMap_app_ofSection, frobeniusMap_app_ofSection,
    scalarMap_app_ofSection, mul_pow, map_pow]

section OverField

open Stacks.Sheaves.UniverseLift

variable (k : Type u) [Field k] {X} (f : X ⟶ Spec (.of k))
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The comparison of `Hⁿ⁺¹(X, 𝒪_X)` with the étale cohomology of `𝐆_a`**, for a scheme over
a field, with the `k`-vector space structure on the source. -/
def cohomologyOverFieldAddEquivSheafH (n : ℕ) :
    cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) (n + 1) ≃+
      Sheaf.H.{w} (additiveSheaf.{u, v} X) (n + 1) :=
  ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
      (n + 1)).app (SheafOfModules.unit X.ringCatSheaf)).addCommGroupIsoToAddEquiv.trans
    (hgroupAddEquivSheafHAdditiveSheaf.{w, v} X n)

/-- **The comparison carries the `k`-action to multiplication by global functions**: the action of
`a ∈ k` on `Hⁿ⁺¹(X, 𝒪_X)` becomes `Hⁿ⁺¹` of `Stacks.ArtinSchreier.scalarMap` at the image of `a` in
`Γ(X, 𝒪_X)`. -/
theorem cohomologyOverFieldAddEquivSheafH_smul (n : ℕ) (a : k)
    (x : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) (n + 1)) :
    cohomologyOverFieldAddEquivSheafH k f n (a • x) =
      Sheaf.H.map (scalarMap.{u, v} X (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a)) (n + 1)
        (cohomologyOverFieldAddEquivSheafH k f n x) := by
  set c := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a
  let : Linear k X.Modules := modulesLinear k (Over.mk f)
  let ψ' := (fullyFaithfulUliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology).preimage
    ((uliftAssociatedUnitIsoAdditiveSheaf.{v} X).hom ≫
      scalarMap.{u, v} X c ≫
        (uliftAssociatedUnitIsoAdditiveSheaf.{v} X).inv)
  have hmap := Functor.FullyFaithful.map_preimage
    (fullyFaithfulUliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology)
    ((uliftAssociatedUnitIsoAdditiveSheaf.{v} X).hom ≫
      scalarMap.{u, v} X c ≫
        (uliftAssociatedUnitIsoAdditiveSheaf.{v} X).inv)
  have h₂ : (uliftSheafFunctor.{max (u + 1) v, u} X.smallEtaleTopology).map ψ' ≫
      (uliftAssociatedUnitIsoAdditiveSheaf.{v} X).hom =
      (uliftAssociatedUnitIsoAdditiveSheaf.{v} X).hom ≫
        scalarMap.{u, v} X c := by
    rw [hmap]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h₁ : (SheafOfModules.toSheaf X.ringCatSheaf).map
        (a • 𝟙 (Scheme.unitModule X)) ≫
        (smallEtaleSectionsUnitIso X (Scheme.unitModule X)).hom =
      (smallEtaleSectionsUnitIso X (Scheme.unitModule X)).hom ≫
        (smallEtaleZariskiPushforward X).map ψ' := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ AddCommGrpCat.ext fun s ↦ ?_))
    let W : X.Opens := V.unop
    let s' : Γ(Scheme.unitModule X, W) := s
    have hle : (⊤ : (W : Scheme.{u}).Opens) ≤ W.ι ⁻¹ᵁ W :=
      Scheme.Opens.top_le_ι_preimage le_rfl
    have hψ := congrArg (fun χ ↦ (χ.hom.app (op ((opensToEtale X).obj W))).hom
        (ULift.up (pullbackSectionHom W.ι (Scheme.unitModule X) W ⊤ hle s))) hmap
    have hr : W.ι.appLE W ⊤ hle
        (X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op
          c) =
        W.ι.appTop c := by
      rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE, appLE_top_top_eq_appTop]
    have hs := pullbackUnitIso_hom_app_pullbackSectionHom_smul W.ι W ⊤ hle
      (X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op
        c) s'
    rw [hr] at hs
    have hinv : ∀ z, (Scheme.Modules.pullbackUnitIso W.ι).inv.app ⊤
        ((Scheme.Modules.pullbackUnitIso W.ι).hom.app ⊤ z) = z := fun z ↦ by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
        Scheme.Modules.Hom.id_app]
      rfl
    exact (hinv _).symm.trans ((congrArg (fun z ↦ (Scheme.Modules.pullbackUnitIso W.ι).inv.app ⊤ z)
      hs).trans (congrArg ULift.down hψ).symm)
  have hfor := ConcreteCategory.congr_hom
    ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤
      (n + 1)).hom.naturality
        (a • 𝟙 (Scheme.unitModule X))) x
  refine (congrArg (cohomologyOverFieldAddEquivSheafH k f n)
    (cohomologyOverField_smul_eq k f (SheafOfModules.unit X.ringCatSheaf) (n + 1) a x)).trans ?_
  exact (congrArg (hgroupAddEquivSheafHAdditiveSheaf.{w, v} X n) hfor).trans
    (hgroupAddEquivSheafHAdditiveSheaf_naturality X _ ψ' _ h₁ h₂ n _)

/-- **The comparison of `H⁰(X, 𝒪_X)` with the étale cohomology of `𝐆_a` in degree zero**: both
are the global functions on `X`, the étale side read at the final object `X` of the small étale
site. -/
def cohomologyOverFieldZeroAddEquivSheafH :
    cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0 ≃+
      Sheaf.H.{w} (additiveSheaf.{u, v} X) 0 :=
  (cohomologyOverFieldZeroIsoSections k f
      (SheafOfModules.unit X.ringCatSheaf)).toLinearEquiv.toAddEquiv.trans
    ((Scheme.Opens.topIso (⊤ : X.Opens)).commRingCatIsoToRingEquiv.symm.toAddEquiv.trans
      (AddEquiv.ulift.symm.trans
        (Sheaf.H.equiv₀ (additiveSheaf.{u, v} X) (isTerminal_opensToEtale_top X)).symm))

/-- `cohomologyOverFieldZeroAddEquivSheafH` on a class: the global function it is, read as a
section of `𝐆_a` over the final object and then as a class in degree zero. -/
theorem cohomologyOverFieldZeroAddEquivSheafH_apply
    (x : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) :
    cohomologyOverFieldZeroAddEquivSheafH k f x =
      (Sheaf.H.equiv₀ (additiveSheaf.{u, v} X) (isTerminal_opensToEtale_top X)).symm
        (ofSection ((Scheme.Opens.topIso (⊤ : X.Opens)).inv
          ((cohomologyOverFieldZeroIsoSections k f (SheafOfModules.unit X.ringCatSheaf)).hom x))) :=
  rfl

/-- **In degree zero the comparison carries the `k`-action to multiplication by global
functions.** -/
theorem cohomologyOverFieldZeroAddEquivSheafH_smul (a : k)
    (x : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) :
    cohomologyOverFieldZeroAddEquivSheafH k f (a • x) =
      Sheaf.H.map (scalarMap.{u, v} X (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a)) 0
        (cohomologyOverFieldZeroAddEquivSheafH k f x) := by
  have hι : (⊤ : X.Opens).ι.appTop = (Scheme.Opens.topIso (⊤ : X.Opens)).inv := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact congrArg (fun i ↦ X.presheaf.map (Quiver.Hom.op i)) (Subsingleton.elim _ _)
  obtain ⟨y, hy⟩ : ∃ y : Γ(X, ⊤),
      y = (cohomologyOverFieldZeroIsoSections k f (SheafOfModules.unit X.ringCatSheaf)).hom x :=
    ⟨_, rfl⟩
  have hs : (cohomologyOverFieldZeroIsoSections k f (SheafOfModules.unit X.ringCatSheaf)).hom
      (a • x) = (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a * y : Γ(X, ⊤)) := by
    rw [hy]
    exact (cohomologyOverFieldZeroIsoSections k f
      (SheafOfModules.unit X.ringCatSheaf)).hom.hom.map_smul a x
  have hc : (Scheme.Opens.topIso (⊤ : X.Opens)).inv (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a) =
      ((opensToEtale X).obj ⊤).hom.appTop (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a) :=
    (congrArg (fun g : Γ(X, ⊤) ⟶ Γ((⊤ : X.Opens), ⊤) ↦ g (((Scheme.ΓSpecIso (.of k)).inv ≫
      f.appTop) a)) hι).symm
  rw [cohomologyOverFieldZeroAddEquivSheafH_apply, cohomologyOverFieldZeroAddEquivSheafH_apply,
    Sheaf.H.equiv₀_symm_naturality]
  refine congrArg (Sheaf.H.equiv₀ _ _).symm ((congrArg ofSection ?_).trans
    (scalarMap_app_ofSection X _ _ _).symm)
  exact (congrArg (fun z ↦ (Scheme.Opens.topIso (⊤ : X.Opens)).inv z) hs).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) hc
      (congrArg (fun z ↦ (Scheme.Opens.topIso (⊤ : X.Opens)).inv z) hy)))

/-- **The comparison of `Hᵈ(X, 𝒪_X)` with `Hᵈ(X_étale, 𝐆_a)` in every degree `d`**, carrying the
action of `a ∈ k` to `Hᵈ` of multiplication by the image of `a` in `Γ(X, 𝒪_X)`: in degree zero it
is `cohomologyOverFieldZeroAddEquivSheafH`, in positive degree `cohomologyOverFieldAddEquivSheafH`.
-/
theorem exists_addEquiv_cohomologyOverField_sheafH (d : ℕ) :
    ∃ E : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d ≃+
      Sheaf.H.{w} (additiveSheaf.{u, v} X) d, ∀ (a : k) x, E (a • x) =
        Sheaf.H.map (scalarMap.{u, v} X (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a)) d
          (E x) := by
  cases d with
  | zero => exact ⟨_, cohomologyOverFieldZeroAddEquivSheafH_smul k f⟩
  | succ n => exact ⟨_, cohomologyOverFieldAddEquivSheafH_smul k f n⟩

end OverField

/-- **The Artin–Schreier map `F - 1` is surjective on the étale cohomology of `𝐆_a`** in every
degree `d`, for a scheme `X` over an algebraically closed field `k` of characteristic `p > 0`
whose cohomology `Hᵈ(X, 𝒪_X)` is a finite-dimensional `k`-vector space. -/
@[sga "1 XI 6.10" "more general", sga "4½ Fonctions_L 3.7" "special case"]
theorem surjective_sheafH_map_artinSchreierMap {p : ℕ} (hp : p.Prime) (k : Type u) [Field k]
    [IsAlgClosed k] [CharP k p] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hX : (p : Γ(X, ⊤)) = 0)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (d : ℕ)
    (hfin : FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d)) :
    Function.Surjective (Sheaf.H.map (artinSchreierMap.{u, v} X hp hX) d) := by
  obtain ⟨E, hE⟩ := exists_addEquiv_cohomologyOverField_sheafH.{u, v, w} k f d
  have hΦ : ∀ (a : k) (y : Sheaf.H.{w} (additiveSheaf.{u, v} X) d),
      Sheaf.H.map (frobeniusMap.{u, v} X hp hX) d
          (Sheaf.H.map (scalarMap.{u, v} X (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a)) d y) =
        Sheaf.H.map (scalarMap.{u, v} X (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) (a ^ p))) d
          (Sheaf.H.map (frobeniusMap.{u, v} X hp hX) d y) := by
    intro a y
    rw [← Sheaf.H.map_comp_apply, scalarMap_comp_frobeniusMap, Sheaf.H.map_comp_apply, map_pow]
  intro y
  obtain ⟨x, hx⟩ := surjective_sub_self_of_addEquiv hp.pos k E _ _ hE hΦ y
  exact ⟨x, (Sheaf.H.map_sub_apply _ _ d x).trans
    ((congrArg (_ - ·) (Sheaf.H.map_id_apply x)).trans hx)⟩

end Stacks.ArtinSchreier

end
