module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaSectionsSplit
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaPullbackFlatTerms
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaGeneratorSection
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedBerthelotOgus
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaQuasicoherent
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalAffine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal
public import StacksFrontier.Algebra.Module.Projective.SplitInjectiveRank
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace

/-!
# The comparison of décalages under a pullback, on an affine chart

Let `g : V ⟶ U` be a morphism of affine schemes, `D ⊆ U` an effective Cartier divisor whose
pullback along `g` is defined, with equation `f ∈ Γ(U, 𝒪_U)`, and `N^•` a complex of flat
quasi-coherent `𝒪_U`-modules whose complex of global sections is isomorphic to a bounded
complex `C^•` of finite free `Γ(U, 𝒪_U)`-modules all of whose determinantal ideals
`I_n(C^•, f)` are principal.  This file proves that the derived comparison of décalages

`Lg^*[η_{ℐ_D} N^•] ⟶ [η_{ℐ_{g^{-1}D}}(g^* N^•)]`

is an isomorphism, with no hypothesis on `g`.

The proof is degreewise.  By Stacks 0F7W (read on sections through Stacks 0F8M) the module
`Γ(U, (η N)^n)` is finite projective of rank `rank Cⁿ`, and its inclusion into
`Γ(U, ℐ^n N^n) × Γ(U, ℐ^{n+1} N^{n+1})` by the two projections of the fibre product defining
`(η N)^n` has a retraction.  So `η N^•` is a bounded above complex of finite locally free
modules, hence K-flat, and the comparison of Stacks 06YJ at it is an isomorphism.  On `V`, the
global sections of `g^*(η N)^n` are the base change of those of `(η N)^n`, so the chain-level
comparison has, on global sections, a retraction; its target is, by the same two tags applied
to the presentation `C^• ⊗ Γ(V, 𝒪_V)` of `Γ(V, g^* N^•)` (the determinantal ideals of which are
principal by Stacks 0GSU), finite projective of the same rank.  A split injection between finite
projective modules of the same rank is bijective, and a map of quasi-coherent modules on an
affine scheme which is bijective on global sections is an isomorphism.

## Main results

* `Stacks.Divisors.Eta.bcTop_hom_naturality`: the base change identification of global sections
  of a pullback along a morphism of affine schemes is natural.
* `Stacks.Divisors.Eta.isIso_divisorPullbackEtaMap_of_isAffine`: the chain-level comparison is an
  isomorphism of complexes.
* `Stacks.Divisors.Eta.isIso_divisorPullbackEtaKFlatComparison_of_isAffine`: the derived
  comparison is an isomorphism.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

open Stacks.IdealTorsion.Eta (etaObj etaTerm etaFst etaSnd pullbackComplex sectionsFunctor
  sectionsComplex generatorSection)
open Stacks.AlgebraicGeometry.ModuleLimits (bcTop appTopHom)

universe u

namespace Stacks.Divisors.Eta

attribute [local instance] Stacks.Divisors.Eta.etaHasDerivedCategory

/-! ### Linear algebra -/

/-- **A retraction pair transports along an additive functor and isomorphisms.**  If
`a_U ≫ ρ₁ + b_U ≫ ρ₂ = 𝟙`, and `a`, `b` are identified with `E(a_U)`, `E(b_U)` by
isomorphisms, then `a`, `b` have the transported retraction pair. -/
theorem comp_add_comp_eq_id_of_iso {C D : Type*} [Category C] [Preadditive C] [Category D]
    [Preadditive D] (E : C ⥤ D) [E.Additive] {SU P₁U P₂U : C} {S P₁ P₂ : D}
    (aU : SU ⟶ P₁U) (bU : SU ⟶ P₂U) (ρ₁ : P₁U ⟶ SU) (ρ₂ : P₂U ⟶ SU)
    (hρ : aU ≫ ρ₁ + bU ≫ ρ₂ = 𝟙 SU)
    (βS : E.obj SU ≅ S) (β₁ : E.obj P₁U ≅ P₁) (β₂ : E.obj P₂U ≅ P₂) (a : S ⟶ P₁) (b : S ⟶ P₂)
    (ha : βS.hom ≫ a = E.map aU ≫ β₁.hom) (hb : βS.hom ≫ b = E.map bU ≫ β₂.hom) :
    a ≫ (β₁.inv ≫ E.map ρ₁ ≫ βS.hom) + b ≫ (β₂.inv ≫ E.map ρ₂ ≫ βS.hom) = 𝟙 S := by
  obtain rfl : a = βS.inv ≫ E.map aU ≫ β₁.hom := by rw [← ha, Iso.inv_hom_id_assoc]
  obtain rfl : b = βS.inv ≫ E.map bU ≫ β₂.hom := by rw [← hb, Iso.inv_hom_id_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← E.map_comp_assoc, ← E.map_comp_assoc, ← Preadditive.comp_add, ← Preadditive.add_comp,
    ← E.map_add, hρ, E.map_id, Category.id_comp, Iso.inv_hom_id]

/-- **A retraction pair pulls back along a map commuting with it up to isomorphisms.** -/
theorem comp_retraction_eq_id {C : Type*} [Category C] [Preadditive C]
    {S T P₁ P₂ P₁' P₂' : C} (t : S ⟶ T) (a' : T ⟶ P₁') (b' : T ⟶ P₂') (a : S ⟶ P₁)
    (b : S ⟶ P₂) (τ₁ : P₁ ≅ P₁') (τ₂ : P₂ ≅ P₂') (R₁ : P₁ ⟶ S) (R₂ : P₂ ⟶ S)
    (ht₁ : t ≫ a' = a ≫ τ₁.hom) (ht₂ : t ≫ b' = b ≫ τ₂.hom) (h : a ≫ R₁ + b ≫ R₂ = 𝟙 S) :
    t ≫ (a' ≫ τ₁.inv ≫ R₁ + b' ≫ τ₂.inv ≫ R₂) = 𝟙 S := by
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc t, ht₁, ht₂, Category.assoc,
    Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id_assoc, h]

/-- **Extension of scalars of a finite projective module of constant rank** is finite projective
of the same rank. -/
theorem finite_projective_rankAtStalk_extendScalars {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M] (r : ℕ)
    (hM : Module.rankAtStalk (R := A) M = fun _ => r) :
    Module.Finite B ((ModuleCat.extendScalars φ).obj M) ∧
      Module.Projective B ((ModuleCat.extendScalars φ).obj M) ∧
        Module.rankAtStalk (R := B) ((ModuleCat.extendScalars φ).obj M) = fun _ => r := by
  let _ := φ.toAlgebra
  refine ⟨inferInstanceAs (Module.Finite B (TensorProduct A B M)),
    inferInstanceAs (Module.Projective B (TensorProduct A B M)), ?_⟩
  funext p
  exact (Module.rankAtStalk_baseChange (R := A) (S := B) (M := M) p).trans (congrFun hM _)

/-! ### Global sections of a pullback between affine schemes -/

/-- **The base change identification of global sections is natural**: for `χ : F ⟶ G` between
quasi-coherent modules on an affine scheme and `f` a morphism of affine schemes,
`Γ(f^*χ)` is the base change of `Γ(χ)`. -/
theorem bcTop_hom_naturality {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (χ : F ⟶ G) :
    (bcTop f F).hom ≫ appTopHom ((Scheme.Modules.pullback f).map χ) =
      (ModuleCat.extendScalars (Scheme.Hom.appTop f).hom).map (appTopHom χ) ≫
        (bcTop f G).hom := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.extendScalars_hom_ext' _ fun m x hx => ?_
  subst hx
  change appTopHom ((Scheme.Modules.pullback f).map χ) ((bcTop f F).hom
      ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤), (Scheme.Hom.appTop f).hom] m)) =
    (bcTop f G).hom ((ModuleCat.extendScalars (Scheme.Hom.appTop f).hom).map (appTopHom χ)
      ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤), (Scheme.Hom.appTop f).hom] m))
  rw [ModuleCat.ExtendScalars.map_tmul]
  refine (congrArg (appTopHom ((Scheme.Modules.pullback f).map χ))
    (Stacks.AlgebraicGeometry.ModuleLimits.bcTop_hom_one_tmul f F m)).trans ?_
  refine Eq.trans ?_ (Stacks.AlgebraicGeometry.ModuleLimits.bcTop_hom_one_tmul f G
    (appTopHom χ m)).symm
  exact Scheme.Modules.pullbackSection_naturality f χ ⊤ ⊤ _ m

/-- A quasi-coherent module on an affine scheme with no nonzero global section is zero. -/
theorem isZero_of_subsingleton_sections_top {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] (h : Subsingleton Γ(M, ⊤)) : IsZero M := by
  have : IsIso (0 : M ⟶ M) :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _
      ((ConcreteCategory.isIso_iff_bijective _).mpr
        ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨y, Subsingleton.elim _ _⟩⟩)
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : M ⟶ M), zero_comp]

/-- A principal equation `f` of an effective Cartier divisor on an affine scheme is the image of a
generator `s` of the ideal sheaf, which is regular and has principal determinantal ideals. -/
private theorem exists_generatesIdealOn_regular_isPrincipal_idealI {W : Scheme.{u}} [IsAffine W]
    (D : W.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) {f : Γ(W, ⊤)}
    (hf : D.ideal ⟨⊤, isAffineOpen_top W⟩ = Ideal.span {f}) (C : BoundedComplex Γ(W, ⊤))
    (hI : ∀ n : ℤ, (idealI C f n).IsPrincipal) :
    ∃ s : (idealSheaf D).val.obj (op ⊤),
      Stacks.IdealTorsion.GeneratesIdealOn W.toRingedSpace ⊤ s ∧
        IsRegular (generatorSection W.toRingedSpace (idealSheafι D) ⊤ s) ∧
          ∀ k : ℤ,
            (idealI C (generatorSection W.toRingedSpace (idealSheafι D) ⊤ s) k).IsPrincipal := by
  have hfnzd := mem_nonZeroDivisors_of_ideal_eq_span D hD ⟨⊤, isAffineOpen_top W⟩ hf
  obtain ⟨s, hs, hsf⟩ :=
    exists_generatesIdealOn_of_ideal_eq_span D ⟨⊤, isAffineOpen_top W⟩ hf hfnzd
  have hsf₀ : generatorSection W.toRingedSpace (idealSheafι D) ⊤ s = f := hsf
  rw [← hsf₀] at hI
  exact ⟨s, hs, hsf₀ ▸ isRegular_iff_mem_nonZeroDivisors.mpr hfnzd, hI⟩

variable {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (g : V ⟶ U)

/-- **The complex of global sections of a pullback is the base change of the complex of global
sections**, for a complex of quasi-coherent modules and a morphism of affine schemes. -/
def sectionsPullbackComplexIso
    (N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf U.toRingedSpace.sheaf)) ℤ)
    (hqc : ∀ n : ℤ, (N.X n).IsQuasicoherent) :
    ((ModuleCat.extendScalars (Scheme.Hom.appTop g).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (sectionsComplex U.toRingedSpace N ⊤) ≅
      sectionsComplex V.toRingedSpace (pullbackComplex g.toLRSHom.toShHom N) ⊤ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => @bcTop _ _ _ _ g (N.X n) (hqc n))
    (fun i j _ => @bcTop_hom_naturality _ _ _ _ g _ _ (hqc i) (hqc j) (N.d i j))

/-! ### The comparison on an affine chart -/

variable (D : U.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [hD : Stacks.Divisors.IsPullbackDefined g D]
  (N : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf U.toRingedSpace.sheaf)) ℤ)
  (hN : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
    (O := U.toRingedSpace.sheaf) (N.X n))
  (hqc : ∀ n : ℤ, (N.X n).IsQuasicoherent)
  (f : Γ(U, ⊤)) (hf : D.ideal ⟨⊤, isAffineOpen_top U⟩ = Ideal.span {f})
  (C : BoundedComplex Γ(U, ⊤)) (eC : sectionsComplex U.toRingedSpace N ⊤ ≅ C.toCochainComplex)
  (hI : ∀ n : ℤ, (idealI C f n).IsPrincipal)

include hqc hf eC hI in
/-- **The chain-level comparison of décalages is an isomorphism in every degree**, on an affine
chart. -/
theorem isIso_divisorPullbackEtaMap_f_of_isAffine (n : ℤ) :
    IsIso ((divisorPullbackEtaMap g D N hN).f n) := by
  obtain ⟨s, hs, hreg, hIs⟩ :=
    exists_generatesIdealOn_regular_isPrincipal_idealI D inferInstance hf C hI
  let φ : Γ(U, ⊤) →+* Γ(V, ⊤) := (Scheme.Hom.appTop g).hom
  have hf' : (D.comap g).ideal ⟨⊤, isAffineOpen_top V⟩ = Ideal.span {φ f} := by
    rw [Stacks.IdealSheaf.ideal_comap_appLE D g ⟨⊤, isAffineOpen_top U⟩ ⟨⊤, isAffineOpen_top V⟩
      (fun _ _ => trivial), hf, Ideal.map_span, Set.image_singleton]
    have : g.appLE ⊤ ⊤ (fun _ _ => trivial) = g.appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
    rw [this]
  have hI' : ∀ k : ℤ, (idealI (C.baseChange φ) (φ f) k).IsPrincipal := by
    intro k
    obtain ⟨x, hx⟩ := hI k
    refine ⟨φ x, ?_⟩
    rw [← map_idealI_eq_idealI_baseChange, hx]
    exact (Ideal.map_span φ {x}).trans (by rw [Set.image_singleton])
  obtain ⟨s', hs', hreg', hIs'⟩ :=
    exists_generatesIdealOn_regular_isPrincipal_idealI (D.comap g) hD hf' (C.baseChange φ) hI'
  let eC' : sectionsComplex V.toRingedSpace (pullbackComplex g.toLRSHom.toShHom N) ⊤ ≅
      (C.baseChange φ).toCochainComplex :=
    (sectionsPullbackComplexIso g N hqc).symm ≪≫
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso eC ≪≫
      Stacks.Eta.DeterminantalIdeal.baseChangeCochainIso φ C
  obtain ⟨hfinU, hprojU, hrankU⟩ :=
    Stacks.IdealTorsion.Eta.finite_projective_rankAtStalk_sections_etaTerm U.toRingedSpace
      (idealSheaf D) (idealSheafι D) N (isIdealTorsionFree_X D N hN) ⊤ s hs C eC hreg n (hIs n)
  obtain ⟨ρ, hρ⟩ := Stacks.IdealTorsion.Eta.exists_retraction_sectionsEtaFstSnd U.toRingedSpace
    (idealSheaf D) (idealSheafι D) N (isIdealTorsionFree_X D N hN) ⊤ s hs C eC hreg n (hIs n)
  obtain ⟨hfinT, hprojT, hrankT⟩ :=
    Stacks.IdealTorsion.Eta.finite_projective_rankAtStalk_sections_etaTerm V.toRingedSpace
      (idealSheaf (D.comap g)) (idealSheafι (D.comap g)) (pullbackComplex g.toLRSHom.toShHom N)
      (isIdealTorsionFree_pullbackComplex_X g D N hN) ⊤ s' hs' (C.baseChange φ) eC' hreg' n
      (hIs' n)
  have hIqc : (idealSheaf D).IsQuasicoherent :=
    isQuasicoherent_of_isInvertible (idealSheaf D) inferInstance
  have hηqc := isQuasicoherent_etaObj D N hqc (isIdealTorsionFree_X D N hN)
  have hpow : ∀ i j : ℤ,
      (Stacks.IdealTorsion.Eta.idealPowerTerm U.toRingedSpace (idealSheaf D) i
        (N.X j)).IsQuasicoherent :=
    fun i j => isQuasicoherent_idealPowerTerm (idealSheaf D) hIqc (N.X j) (hqc j) i
  let E := ModuleCat.extendScalars φ
  let aU := (sectionsFunctor U.toRingedSpace ⊤).map
    (etaFst U.toRingedSpace (idealSheaf D) (idealSheafι D) N n)
  let bU := (sectionsFunctor U.toRingedSpace ⊤).map
    (etaSnd U.toRingedSpace (idealSheaf D) (idealSheafι D) N n)
  let ρ₁ := ModuleCat.ofHom (ρ ∘ₗ LinearMap.inl _ _ _)
  let ρ₂ := ModuleCat.ofHom (ρ ∘ₗ LinearMap.inr _ _ _)
  have hρU : aU ≫ ρ₁ + bU ≫ ρ₂ = 𝟙 _ := by
    ext x
    change ρ (aU x, 0) + ρ (0, bU x) = x
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    exact LinearMap.congr_fun hρ x
  let βS := @bcTop _ _ _ _ g ((etaObj U.toRingedSpace (idealSheaf D) (idealSheafι D) N
    (isIdealTorsionFree_X D N hN)).X n) (hηqc n)
  let β₁ := @bcTop _ _ _ _ g _ (hpow n n)
  let β₂ := @bcTop _ _ _ _ g _ (hpow (n + 1) (n + 1))
  let a := (sectionsFunctor V.toRingedSpace ⊤).map ((Stacks.RingedSpace.pullbackFunctor
    g.toLRSHom.toShHom).map (etaFst U.toRingedSpace (idealSheaf D) (idealSheafι D) N n))
  let b := (sectionsFunctor V.toRingedSpace ⊤).map ((Stacks.RingedSpace.pullbackFunctor
    g.toLRSHom.toShHom).map (etaSnd U.toRingedSpace (idealSheaf D) (idealSheafι D) N n))
  have ha : βS.hom ≫ a = E.map aU ≫ β₁.hom :=
    @bcTop_hom_naturality _ _ _ _ g _ _ (hηqc n) (hpow n n) _
  have hb : βS.hom ≫ b = E.map bU ≫ β₂.hom :=
    @bcTop_hom_naturality _ _ _ _ g _ _ (hηqc n) (hpow (n + 1) (n + 1)) _
  have hS := comp_add_comp_eq_id_of_iso E aU bU ρ₁ ρ₂ hρU βS β₁ β₂ a b ha hb
  have hfst := @Stacks.IdealTorsion.Eta.transportedPullbackEtaMap_f_fst _ _
    g.toLRSHom.toShHom
    (idealSheaf D) (idealSheafι D) (isInvertible_idealSheaf D)
    (idealSheaf (D.comap g)) (idealSheafι (D.comap g)) (isInvertible_idealSheaf (D.comap g))
    (Stacks.Divisors.pullbackIdealSheafComapIso g D hD) (mono_idealSheafι D)
    (mono_pullbackIdealIncl_of_isPullbackDefined g D inferInstance) (mono_idealSheafι (D.comap g))
    (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι g D hD) N
    (isIdealTorsionFree_X D N hN) (isIdealTorsionFree_pullbackComplex_X' g D N hN)
    (isIdealTorsionFree_pullbackComplex_X g D N hN) n
  have hsnd := @Stacks.IdealTorsion.Eta.transportedPullbackEtaMap_f_snd _ _
    g.toLRSHom.toShHom
    (idealSheaf D) (idealSheafι D) (isInvertible_idealSheaf D)
    (idealSheaf (D.comap g)) (idealSheafι (D.comap g)) (isInvertible_idealSheaf (D.comap g))
    (Stacks.Divisors.pullbackIdealSheafComapIso g D hD) (mono_idealSheafι D)
    (mono_pullbackIdealIncl_of_isPullbackDefined g D inferInstance) (mono_idealSheafι (D.comap g))
    (Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι g D hD) N
    (isIdealTorsionFree_X D N hN) (isIdealTorsionFree_pullbackComplex_X' g D N hN)
    (isIdealTorsionFree_pullbackComplex_X g D N hN) n
  let Sec := sectionsFunctor V.toRingedSpace ⊤
  let t := Sec.map ((divisorPullbackEtaMap g D N hN).f n)
  let a' := Sec.map (etaFst V.toRingedSpace (idealSheaf (D.comap g)) (idealSheafι (D.comap g))
    (pullbackComplex g.toLRSHom.toShHom N) n)
  let b' := Sec.map (etaSnd V.toRingedSpace (idealSheaf (D.comap g)) (idealSheafι (D.comap g))
    (pullbackComplex g.toLRSHom.toShHom N) n)
  let τ₁ := Sec.mapIso (Stacks.IdealTorsion.Eta.pullbackIdealPowerTransportIso g.toLRSHom.toShHom
    (idealSheaf D) (idealSheaf (D.comap g)) (Stacks.Divisors.pullbackIdealSheafComapIso g D hD)
    n (N.X n))
  let τ₂ := Sec.mapIso (Stacks.IdealTorsion.Eta.pullbackIdealPowerTransportIso g.toLRSHom.toShHom
    (idealSheaf D) (idealSheaf (D.comap g)) (Stacks.Divisors.pullbackIdealSheafComapIso g D hD)
    (n + 1) (N.X (n + 1)))
  have ht₁ : t ≫ a' = a ≫ τ₁.hom :=
    (Sec.map_comp _ _).symm.trans ((congrArg Sec.map hfst).trans (Sec.map_comp _ _))
  have ht₂ : t ≫ b' = b ≫ τ₂.hom :=
    (Sec.map_comp _ _).symm.trans ((congrArg Sec.map hsnd).trans (Sec.map_comp _ _))
  let R₁ := β₁.inv ≫ E.map ρ₁ ≫ βS.hom
  let R₂ := β₂.inv ≫ E.map ρ₂ ≫ βS.hom
  have hT : t ≫ (a' ≫ τ₁.inv ≫ R₁ + b' ≫ τ₂.inv ≫ R₂) = 𝟙 _ :=
    comp_retraction_eq_id t a' b' a b τ₁ τ₂ R₁ R₂ ht₁ ht₂ hS
  obtain ⟨hfinE, hprojE, hrankE⟩ :=
    @finite_projective_rankAtStalk_extendScalars _ _ _ _ φ _ hfinU hprojU _ hrankU
  have hfinS : Module.Finite (V.toRingedSpace.presheaf.obj (op ⊤))
      (Sec.obj ((pullbackComplex g.toLRSHom.toShHom
      (etaObj U.toRingedSpace (idealSheaf D) (idealSheafι D) N
        (isIdealTorsionFree_X D N hN))).X n)) :=
    @Module.Finite.equiv _ _ _ _ _ _ _ _ hfinE βS.toLinearEquiv
  have hprojS : Module.Projective (V.toRingedSpace.presheaf.obj (op ⊤))
      (Sec.obj ((pullbackComplex g.toLRSHom.toShHom
      (etaObj U.toRingedSpace (idealSheaf D) (idealSheafι D) N
        (isIdealTorsionFree_X D N hN))).X n)) :=
    @Module.Projective.of_equiv _ _ _ _ _ _ _ _ _ _ _ _ _ _ βS.toLinearEquiv hprojE
  have hrankS := (Module.rankAtStalk_eq_of_equiv βS.toLinearEquiv).symm.trans hrankE
  have hbij := @Module.bijective_of_retraction_of_rankAtStalk_eq _ _ _ _ _ _ _ _ hfinS hprojS
    hfinT hprojT t.hom (a' ≫ τ₁.inv ≫ R₁ + b' ≫ τ₂.inv ≫ R₂).hom
    ((ModuleCat.hom_comp _ _).symm.trans ((congrArg ModuleCat.Hom.hom hT).trans ModuleCat.hom_id))
    (hrankS.trans hrankT.symm)
  have hsrc : ((Scheme.Modules.pullback g).obj ((etaObj U.toRingedSpace (idealSheaf D)
      (idealSheafι D) N (isIdealTorsionFree_X D N hN)).X n)).IsQuasicoherent :=
    @Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _ g _ (hηqc n)
  have htgt := isQuasicoherent_etaObj (D.comap g) (pullbackComplex g.toLRSHom.toShHom N)
    (fun k => @Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _ g _ (hqc k))
    (isIdealTorsionFree_pullbackComplex_X g D N hN) n
  exact @Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top V _ _ _ hsrc htgt _
    ((ConcreteCategory.isIso_iff_bijective _).mpr hbij)

include hqc hf eC hI in
/-- **The chain-level comparison of décalages is an isomorphism of complexes**, on an affine
chart. -/
theorem isIso_divisorPullbackEtaMap_of_isAffine :
    IsIso (divisorPullbackEtaMap g D N hN) := by
  have := isIso_divisorPullbackEtaMap_f_of_isAffine g D N hN hqc f hf C eC hI
  exact HomologicalComplex.Hom.isIso_of_components _

omit [IsAffine V] hD in
include hqc hf eC hI in
/-- **The décalage of a complex with a presentation on an affine chart is K-flat**: by
Stacks 0F7W its terms have finite projective global sections, of rank `rank Cⁿ`, so they are
finite locally free, hence flat, and they vanish in large degrees. -/
theorem kFlat_etaObj_of_isAffine :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex U.toRingedSpace
      (etaObj U.toRingedSpace (idealSheaf D) (idealSheafι D) N (isIdealTorsionFree_X D N hN)) := by
  obtain ⟨s, hs, hreg, hIs⟩ :=
    exists_generatesIdealOn_regular_isPrincipal_idealI D inferInstance hf C hI
  have hηqc := isQuasicoherent_etaObj D N hqc (isIdealTorsionFree_X D N hN)
  have hfp := fun n : ℤ =>
    Stacks.IdealTorsion.Eta.finite_projective_rankAtStalk_sections_etaTerm U.toRingedSpace
      (idealSheaf D) (idealSheafι D) N (isIdealTorsionFree_X D N hN) ⊤ s hs C eC hreg n (hIs n)
  obtain ⟨n₀, hn₀⟩ := C.bounded.bddAbove
  refine AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat
    U.toRingedSpace _ ⟨n₀, (CochainComplex.isStrictlyLE_iff _ _).mpr fun i hi => ?_⟩ fun i => ?_
  · obtain ⟨hfin, hproj, hrank⟩ := hfp i
    have hzero : C.rank i = 0 := by
      by_contra h
      exact absurd (hn₀ h) (not_le.mpr hi)
    have hsub := (@Module.rankAtStalk_eq_zero_iff_subsingleton _ _ _ _ _
      (@Module.Flat.of_projective _ _ _ _ _ hproj) hfin).mp (by rw [hrank, hzero]; rfl)
    exact @isZero_of_subsingleton_sections_top U _ _ (hηqc i) hsub
  · obtain ⟨hfin, hproj, -⟩ := hfp i
    have hlf : Module.IsFiniteLocallyFree (U.toRingedSpace.presheaf.obj (op ⊤))
        ((sectionsFunctor U.toRingedSpace ⊤).obj
          ((etaObj U.toRingedSpace (idealSheaf D) (idealSheafι D) N
            (isIdealTorsionFree_X D N hN)).X i)) :=
      (Module.isFiniteLocallyFree_iff_finite_projective _ _).mpr ⟨hfin, hproj⟩
    exact AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
      ((Scheme.Modules.isFiniteLocallyFree_iff _).mp
        (@Stacks.BlowUpComplexes.isFiniteLocallyFree_of_module_affineOpens U _ (hηqc i)
          fun _ => ⟨⟨⊤, isAffineOpen_top U⟩, trivial, hlf⟩))

include hqc hf eC hI in
/-- **On an affine chart the derived comparison of décalages is an isomorphism**: for a morphism
`g : V ⟶ U` of affine schemes, an effective Cartier divisor `D ⊆ U` with equation `f` whose
pullback along `g` is defined, and a complex `N^•` of flat quasi-coherent `𝒪_U`-modules whose
complex of global sections is isomorphic to a bounded complex `C^•` of finite free modules with
principal determinantal ideals `I_n(C^•, f)`, the comparison
`Lg^*[η_{ℐ_D} N^•] ⟶ [η_{ℐ_{g^{-1}D}}(g^* N^•)]` is an isomorphism. -/
theorem isIso_divisorPullbackEtaKFlatComparison_of_isAffine :
    IsIso (divisorPullbackEtaKFlatComparison g D N hN) := by
  have hc := Stacks.IdealTorsion.Eta.isIso_etaPullbackComparisonOnComplex g.toLRSHom.toShHom _
    (kFlat_etaObj_of_isAffine D N hN hqc f hf C eC hI)
  have := isIso_divisorPullbackEtaMap_of_isAffine g D N hN hqc f hf C eC hI
  have : IsIso (DerivedCategory.Q.map (divisorPullbackEtaMap g D N hN)) := inferInstance
  exact IsIso.comp_isIso' hc this

end Stacks.Divisors.Eta

end
