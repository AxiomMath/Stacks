module

public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Perfect.SingleDegreeFibre
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A bounded complex of projectives which is free in one degree after base change to a field

Let `R` be a commutative ring, `L` a bounded complex of finite projective `R`-modules and
`φ : R → k` a ring map to a field. If the cohomology of `L ⊗_R k` vanishes outside degree `i`
and has dimension `n` in degree `i`, then on a principal neighbourhood `D(g)` of the point
`ker φ` the complex `L` is homotopy equivalent to the free module `R_g^n` placed in degree `i`.

This is the local input to the universal property of the locus where a perfect complex is a
locally free module of rank `n` in degree `i`: it is [stacks 0BCD] at the prime `ker φ`, with the
derived fibre computed degreewise and compared with the fibre over the extension `κ(ker φ) → k`.

## Main results

* `StacksDraft.Perfect.nonempty_homotopyEquiv_of_Q_iso`: an isomorphism in the derived category
  between K-projective complexes comes from a homotopy equivalence.
* `StacksDraft.Perfect.exists_away_homotopyEquiv_single_of_finrank_homology`: the principal
  neighbourhood and the homotopy equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- An isomorphism in the derived category between two K-projective complexes is induced by a
homotopy equivalence. -/
theorem nonempty_homotopyEquiv_of_Q_iso {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (M N : CochainComplex C ℤ) [M.IsKProjective] [N.IsKProjective]
    (e : (DerivedCategory.Q).obj M ≅ (DerivedCategory.Q).obj N) :
    Nonempty (HomotopyEquiv M N) := by
  let E : (DerivedCategory.Qh).obj ((HomotopyCategory.quotient _ _).obj M) ≅
      (DerivedCategory.Qh).obj ((HomotopyCategory.quotient _ _).obj N) :=
    (DerivedCategory.quotientCompQhIso _).app M ≪≫ e ≪≫
      ((DerivedCategory.quotientCompQhIso _).app N).symm
  obtain ⟨f, hf⟩ := (CochainComplex.IsKProjective.Qh_map_bijective M _).surjective E.hom
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective N _).surjective E.inv
  have hfg : f ≫ g = 𝟙 _ := (CochainComplex.IsKProjective.Qh_map_bijective M _).injective (by
    rw [Functor.map_comp, hf, hg, E.hom_inv_id]
    simp)
  have hgf : g ≫ f = 𝟙 _ := (CochainComplex.IsKProjective.Qh_map_bijective N _).injective (by
    rw [Functor.map_comp, hg, hf, E.inv_hom_id]
    simp)
  exact ⟨HomotopyCategory.homotopyEquivOfIso
    { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }⟩

variable {R : Type u} [CommRing R]

/-- Degreewise extension of scalars of a bounded complex of projectives computes the total
derived extension of scalars. -/
theorem nonempty_totalDerivedExtensionScalars_obj_Q_iso {A : Type u} [CommRing A] (f : R →+* A)
    (L : CochainComplex (ModuleCat.{max v u} R) ℤ) (b : ℤ) [L.IsStrictlyLE b]
    [∀ j, Projective (L.X j)] :
    Nonempty ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj ((DerivedCategory.Q).obj L) ≅
      (DerivedCategory.Q).obj
        (((ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) :=
  ⟨@asIso _ _ _ _ ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app L)
    ((totalDerivedExtensionScalars.{u, u, v} f).comparison_isIso_of_projective L b)⟩

/-- Extension of scalars along a homomorphism of fields preserves the dimension of a
finite-dimensional vector space. -/
@[ega "IV 2.5.8.9" "partial"]
theorem finrank_extendScalars_of_field {k l : Type u} [Field k] [Field l] (φ : k →+* l)
    (M : ModuleCat.{max v u} k) [Module.Finite k M] :
    Module.finrank l ((ModuleCat.extendScalars.{u, u, max v u} φ).obj M) = Module.finrank k M := by
  let e : M ≅ ModuleCat.of k (ULift.{v} (Fin (Module.finrank k M) → k)) :=
    ((Module.finBasis k M).equivFun.trans ULift.moduleEquiv.symm).toModuleIso
  obtain ⟨e'⟩ := extendScalars_standard_free_iso.{u, v} φ (Module.finrank k M)
  rw [(((ModuleCat.extendScalars.{u, u, max v u} φ).mapIso e ≪≫ e').toLinearEquiv).finrank_eq]
  simp

/-- **A bounded complex of finite projectives which, after base change to a field, has
cohomology only in degree `i`, of dimension `n`, is homotopy equivalent to `R_g^n` placed in
degree `i` on a principal open `D(g)` containing the point.** -/
theorem exists_away_homotopyEquiv_single_of_finrank_homology {k : Type u} [Field k]
    (φ : R →+* k) (L : CochainComplex (ModuleCat.{max v u} R) ℤ) (a b : ℤ) [L.IsStrictlyGE a]
    [L.IsStrictlyLE b] (hfin : ∀ j, Module.Finite R (L.X j))
    (hproj : ∀ j, Module.Projective R (L.X j)) (i : ℤ) (n : ℕ)
    (hdim : ∀ j, Module.finrank k
      ((((ModuleCat.extendScalars.{u, u, max v u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).homology j) = if j = i then n else 0) :
    ∃ g : R, φ g ≠ 0 ∧ Nonempty (HomotopyEquiv
      (((ModuleCat.extendScalars.{u, u, max v u}
        (algebraMap R (Localization.Away g))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
      ((HomologicalComplex.single (ModuleCat.{max v u} (Localization.Away g))
        (ComplexShape.up ℤ) i).obj
        (ModuleCat.of (Localization.Away g) (ULift.{v} (Fin n → Localization.Away g))))) := by
  classical
  let p := RingHom.ker φ
  have : p.IsPrime := RingHom.ker_isPrime φ
  have hLproj : ∀ j, Projective (L.X j) := fun j => (L.X j).projective_of_categoryTheory_projective
  let K := (DerivedCategory.Q).obj L
  have hK : IsPerfect K := ⟨L, a, b, inferInstance, inferInstance, hfin, hproj, ⟨Iso.refl _⟩⟩
  -- the lift `κ(p) → k`
  have hunit : p.primeCompl ≤ (IsUnit.submonoid k).comap φ := by
    intro x hx
    exact isUnit_iff_ne_zero.2 fun h => hx (RingHom.mem_ker.2 h)
  let ι : p.ResidueField →+* k := Ideal.ResidueField.lift p φ le_rfl hunit
  have hι : ι.comp (algebraMap R p.ResidueField) = φ := by
    ext r
    exact Ideal.ResidueField.lift_algebraMap p φ le_rfl hunit r
  -- the fibre dimensions over `κ(p)` agree with those over `k`
  obtain ⟨hfinH, -, -⟩ := exists_away_bounded_free_complex_representing.{u, v} p K hK
  have hGl : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} ι) := by
    let : Algebra p.ResidueField k := ι.toAlgebra
    refine extendScalars_preservesFiniteLimits_of_flat'.{u, v} ι ?_
    rw [← ι.algebraMap_toAlgebra, RingHom.flat_algebraMap_iff]
    infer_instance
  have hGc : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, max v u} ι) :=
    ModuleCat.extendScalars_preservesFiniteColimits ι
  have hdim0 : ∀ j, Module.finrank p.ResidueField (derivedFibreHomology.{u, v} p K j) =
      if j = i then n else 0 := by
    intro j
    rw [← hdim j]
    obtain ⟨e0⟩ := nonempty_totalDerivedExtensionScalars_obj_Q_iso.{u, v}
      (algebraMap R p.ResidueField) L b
    let C0 := ((ModuleCat.extendScalars.{u, u, max v u}
      (algebraMap R p.ResidueField)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
    let H0 : derivedFibreHomology.{u, v} p K j ≅ C0.homology j :=
      (DerivedCategory.homologyFunctor _ j).mapIso e0 ≪≫
        (DerivedCategory.homologyFunctorFactors _ j).app C0
    have : Module.Finite p.ResidueField (C0.homology j) :=
      Module.Finite.equiv H0.toLinearEquiv
    let G := ModuleCat.extendScalars.{u, u, max v u} ι
    rw [← hι]
    let Hk : (((ModuleCat.extendScalars.{u, u, max v u}
        (ι.comp (algebraMap R p.ResidueField))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).homology j ≅ G.obj (C0.homology j) :=
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).mapIso
        ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, max v u}
          (algebraMap R p.ResidueField) ι) (ComplexShape.up ℤ)).app L) ≪≫
        (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso G
          (ComplexShape.up ℤ) j).app C0
    rw [Hk.toLinearEquiv.finrank_eq, finrank_extendScalars_of_field.{u, v} ι,
      H0.toLinearEquiv.finrank_eq]
  -- the principal neighbourhood
  obtain ⟨g, hg, ⟨e⟩⟩ := exists_away_iso_singleFunctor_free_of_fibre_concentrated.{u, v} p K hK i
    (fun j hj => by rw [hdim0 j, ite_eq_right hj])
  rw [hdim0 i, ite_eq_left rfl] at e
  refine ⟨g, fun h => hg (RingHom.mem_ker.2 h), ?_⟩
  obtain ⟨eg⟩ := nonempty_totalDerivedExtensionScalars_obj_Q_iso.{u, v}
    (algebraMap R (Localization.Away g)) L b
  let Lg := ((ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.Away g))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have : CochainComplex.IsStrictlyLE Lg b := by dsimp only [Lg]; infer_instance
  have : ∀ j, Projective (Lg.X j) := fun j =>
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R (Localization.Away g))).map_projective _
      (hLproj j)
  have : CochainComplex.IsKProjective Lg := CochainComplex.isKProjective_of_projective Lg b
  let F := ModuleCat.of (Localization.Away g) (ULift.{v} (Fin n → Localization.Away g))
  have : Projective F := F.projective_of_categoryTheory_projective
  let S := (HomologicalComplex.single (ModuleCat.{max v u} (Localization.Away g))
    (ComplexShape.up ℤ) i).obj F
  have : CochainComplex.IsStrictlyLE S i := by dsimp only [S]; infer_instance
  have : ∀ j, Projective (S.X j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf _ _ F).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) i F j hj).projective
  have : CochainComplex.IsKProjective S := CochainComplex.isKProjective_of_projective S i
  exact nonempty_homotopyEquiv_of_Q_iso Lg S (eg.symm ≪≫ e ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ i).app F)

/-- A homotopy equivalence over `R_g` between `L ⊗ R_g` and `R_g^n` in degree `i` gives one over
every `R`-algebra in which `g` becomes a unit. -/
theorem nonempty_homotopyEquiv_single_of_isUnit (L : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (g : R) (i : ℤ) (n : ℕ)
    (e : HomotopyEquiv
      (((ModuleCat.extendScalars.{u, u, max v u}
        (algebraMap R (Localization.Away g))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
      ((HomologicalComplex.single (ModuleCat.{max v u} (Localization.Away g))
        (ComplexShape.up ℤ) i).obj
        (ModuleCat.of (Localization.Away g) (ULift.{v} (Fin n → Localization.Away g)))))
    {R'' : Type u} [CommRing R''] (θ : R →+* R'') (hθ : IsUnit (θ g)) :
    Nonempty (HomotopyEquiv
      (((ModuleCat.extendScalars.{u, u, max v u} θ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
      ((HomologicalComplex.single (ModuleCat.{max v u} R'') (ComplexShape.up ℤ) i).obj
        (ModuleCat.of R'' (ULift.{v} (Fin n → R''))))) := by
  let θ' : Localization.Away g →+* R'' := IsLocalization.Away.lift g hθ
  have hθ' : θ'.comp (algebraMap R (Localization.Away g)) = θ := IsLocalization.Away.lift_comp g hθ
  let G := ModuleCat.extendScalars.{u, u, max v u} θ'
  obtain ⟨eF⟩ := extendScalars_standard_free_iso.{u, v} θ' n
  have e₁ : HomotopyEquiv
      (((ModuleCat.extendScalars.{u, u, max v u} θ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, max v u}
          (algebraMap R (Localization.Away g))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) := by
    rw [← hθ']
    exact HomotopyEquiv.ofIso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, max v u}
        (algebraMap R (Localization.Away g)) θ') (ComplexShape.up ℤ)).app L)
  exact ⟨e₁.trans ((G.mapHomotopyEquiv e).trans (HomotopyEquiv.ofIso
    ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) i).app _ ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) i).mapIso eF)))⟩

end StacksDraft.Perfect

end
