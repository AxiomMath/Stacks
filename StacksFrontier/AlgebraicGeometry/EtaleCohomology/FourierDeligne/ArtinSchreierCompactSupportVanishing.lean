module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.TorsorPermutationVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportSheafFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyCoverCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ConstantFiniteModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocalizationAwayPolynomial
public import StacksFrontier.AlgebraicGeometry.CurveAffineOrHProjective.Witness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Hⁱ_c(𝔸¹_k̄, L_ψ) = 0` for a nontrivial additive character `ψ`

Let `k` be a finite field with `q` elements and `ψ` a nontrivial additive character of `k` with
values in a ring `O` over `ℤ_ℓ`. The Artin–Schreier sheaf `L_ψ = L_ψ(x)` on the affine line
`𝔸¹_k = Spec k[x]` (`Stacks.ArtinSchreier.artinSchreierSheaf`) has no compactly supported
cohomology over `k̄`: `Hⁱ_c(𝔸¹_k̄, L_ψ) = 0` for every `i`, at every finite level.

## Main definitions

* `Stacks.ArtinSchreier.affineLineRingEquiv`: the Artin–Schreier cover of the affine line is an
  affine line, `k[x][T]/(T^q - T - x) ≅ k[T]`.
* `Stacks.ArtinSchreier.affineLineASHom`: the Artin–Schreier cover of the affine line, as the
  endomorphism `x ↦ x^q - x` of the affine line.

## Main results

* `Stacks.EtaleCohomology.finite_and_natCard_permModule_eq_of_finiteEtale_endomorphism`: for a
  finite étale endomorphism `g` over `k` of a smooth curve `U`,
  `#Hⁱ_c(U_k̄, ℱ_{ℤ/m[Y]}) = #Hⁱ_c(U_k̄, ℤ/m)`, `Y` a geometric fibre of `g`, and this is finite.
* `Stacks.EtaleCohomology.subsingleton_compactSupportSheafCohomology_of_torsor_character`:
  `Hⁱ_c(U_k̄, ℱ_M) = 0` for a module `M` on which `π₁` acts through the character of a torsor
  cover, isomorphic to a finite étale endomorphism of `U`, by an action without invariants.
* `Stacks.ArtinSchreier.subsingleton_compactSupportSheafCohomology_artinSchreierSheaf_etaleLevel`:
  `Hⁱ_c(𝔸¹_k̄, L_ψ) = 0` at every finite level, for a nontrivial additive character `ψ`.

## References

* [G. Laumon, Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil, 1.2]
* [P. Deligne, SGA 4½, Sommes trigonométriques, 2.7]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- `m` kills every sheaf of `ℤ/m`-modules. -/
theorem nsmul_id_etaleModules_zmod (m : ℕ) {X : Scheme.{u}} (G : EtaleModules.{u, 0} (ZMod m) X) :
    m • 𝟙 G = 0 := by
  apply Sheaf.hom_ext
  ext V x
  show m • x = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod m), ZMod.natCast_self, zero_smul]

section Endomorphism

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] {k : Type u} [Field k]
  [Fintype k] (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  [IsCurve k f] [Smooth f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (m : ℕ) [NeZero m]
  (g : U ⟶ U) [IsFinite (B.inclusion.map g)] [Etale (B.inclusion.map g)] (hgf : g.hom ≫ f = f)
  (hg : finiteEtale g.hom) (y : GeometricPoint U.1)
  [Fintype ((finiteEtaleFiberFunctor (y.map g.hom)).obj (finiteEtaleOverSource hg))]
  (hY : ∀ z : (finiteEtaleFiberFunctor (y.map g.hom)).obj (finiteEtaleOverSource hg),
    IsOpen (MulAction.stabilizer (EtaleFundamentalGroup U.1 (y.map g.hom)) z :
      Set (EtaleFundamentalGroup U.1 (y.map g.hom))))

/-- The compactification `j_V : U ⟶ V̄` of `U` over `k` given by a smooth projective
compactification `V̄` of a finite étale endomorphism `g` of `U` over `k`. -/
def coverCompactificationOfEndomorphism {pUb : j.space ⟶ Spec (.of k)}
    (C : CoverCompactification k pUb j.immersion g.hom) (hC : C.j ≫ C.q = f) :
    CompactificationOf (Over.mk f) :=
  ⟨StructuredArrow.mk (Y := Over.mk C.q) (Over.homMk C.j hC), ⟨C.isOpenImmersion, C.isProper⟩⟩

include hgf in
/-- For the geometric fibre `Y` of a finite étale endomorphism `g` over `k` of a smooth curve `U`
over a finite field `k`, the group `Hⁱ_c(U_k̄, ℱ_{ℤ/m[Y]})` is finite and has as many elements as
`Hⁱ_c(U_k̄, ℤ/m)`. -/
theorem finite_and_natCard_permModule_eq_of_finiteEtale_endomorphism (i : ℤ) :
    Finite ((compactSupportSheafCohomology (ZMod m) f j kbar i).obj
        ((lisseEtaleSheaf B U (y.map g.hom) (ZMod m)).obj (permModule m PUnit.{u + 2} hY))) ∧
      Nat.card ((compactSupportSheafCohomology (ZMod m) f j kbar i).obj
        ((lisseEtaleSheaf B U (y.map g.hom) (ZMod m)).obj (permModule m PUnit.{u + 2} hY))) =
      Nat.card ((compactSupportSheafCohomology (ZMod m) f j kbar i).obj
        ((lisseEtaleSheaf B U (y.map g.hom) (ZMod m)).obj (trivialContinuousModule m))) := by
  let Λ := ZMod m
  let M := ModuleCat.of Λ (ULift.{u + 1} Λ)
  let H := compactSupportSheafCohomology Λ f j kbar i
  have : IsFinite g.hom := inferInstanceAs (IsFinite (B.inclusion.map g))
  have : Etale g.hom := inferInstanceAs (Etale (B.inclusion.map g))
  obtain ⟨i₁⟩ := nonempty_lisseEtaleSheaf_permModule_iso B g y m hg hY
  obtain ⟨i₂⟩ := nonempty_lisseEtaleSheaf_trivialContinuousModule_iso B U y m
  obtain ⟨i₃⟩ := nonempty_lisseEtaleSheaf_trivialContinuousModule_iso B U (y.map g.hom) m
  obtain ⟨C⟩ := nonempty_coverCompactification k f j.toBase j.immersion
    (CompactificationOf.immersion_toBase j) g.hom
  have hC : C.j ≫ C.q = f := by
    rw [C.j_comp_q f (CompactificationOf.immersion_toBase j), hgf]
  let jV := coverCompactificationOfEndomorphism B U f j g C hC
  have : IsIntegralHom (show jV.space ⟶ j.space from C.fb) :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType C.fb).1 C.isFinite).1
  have hφb : C.fb ≫ j.toBase = jV.toBase := C.hq
  have sq : IsPullback g.hom jV.immersion j.immersion C.fb := C.isPullback.flip
  let α := compactSupportSheafCohomologyIntegralIso Λ f j f jV g.hom C.fb hφb sq kbar i
  have hkill : m • 𝟙 (etaleModuleConstantSheaf Λ M U.1) = 0 := nsmul_id_etaleModules_zmod m _
  let β := compactSupportSheafCohomologyCompactificationIso Λ f kbar jV j
    (etaleModuleConstantSheaf Λ M U.1) m (Nat.pos_of_neZero m) hkill i
  let e : H.obj ((lisseEtaleSheaf B U (y.map g.hom) Λ).obj (permModule m PUnit.{u + 2} hY)) ≅
      H.obj ((lisseEtaleSheaf B U (y.map g.hom) Λ).obj (trivialContinuousModule m)) :=
    H.mapIso (i₁ ≪≫ (etaleModuleDirectImage.{u, 0} Λ g.hom).mapIso i₂) ≪≫ (α.app _).symm ≪≫ β ≪≫
      H.mapIso i₃.symm
  have : CompactSpace U.1 := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace U.1 := quasiSeparatedSpace_of_quasiSeparated f
  have hfin : Finite (H.obj (etaleModuleConstantSheaf Λ M U.1)) :=
    finite_compactSupportSheafCohomology_of_isConstructible B U f j kbar
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le m _
      (isConstructibleEtaleModule_constantSheaf_of_finite B U Λ M
        (Module.Finite.equiv (ULift.moduleEquiv (R := Λ)).symm)) i
  refine ⟨Finite.of_equiv _ (e ≪≫ H.mapIso i₃).toLinearEquiv.toEquiv.symm, ?_⟩
  exact Nat.card_congr e.toLinearEquiv.toEquiv

end Endomorphism

/-! ### Torsor covers isomorphic to a finite étale endomorphism -/

section Torsor

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] {k : Type u} [Field k]
  [Fintype k] (f : U.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  [IsCurve k f] [Smooth f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (m : ℕ) [NeZero m]
  (g : U ⟶ U) [IsFinite (B.inclusion.map g)] [Etale (B.inclusion.map g)] (hgf : g.hom ≫ f = f)
  (hg : finiteEtale g.hom) {K : Type u} [AddCommGroup K] [Fintype K]
  (hK : IsUnit (Fintype.card K : ZMod m)) (T : TorsorCover U.1 K)
  (ε : T.cover ≅ finiteEtaleOverSource hg)

include hgf hK hg ε in
/-- **`Hⁱ_c(U_k̄, ℱ_M) = 0` for a module `M` on which `π₁` acts through the character of a torsor
cover with an action of `K` without invariants**, when the torsor cover is a finite étale
endomorphism of the smooth curve `U` over the finite field `k` (`M` free over `ℤ/m`, `#K`
invertible in `ℤ/m`). -/
theorem subsingleton_compactSupportSheafCohomology_of_torsor_character (x : GeometricPoint U.1)
    (p₀ : (finiteEtaleFiberFunctor x).obj T.cover)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup U.1 x))
    (ρ : Multiplicative K →* Module.End (ZMod m) M.obj.obj.obj.V)
    (hM : ∀ (σ : EtaleFundamentalGroup U.1 x) (v : M.obj.obj.obj.V),
      (M.obj.obj.obj.ρ σ).asHom.hom v = ρ (T.character x p₀ σ) v)
    (hfix : ∀ v, ∑ a : K, ρ (Multiplicative.ofAdd a) v = 0)
    {ι : Type (u + 1)} [Fintype ι] [DecidableEq ι]
    (bM : Module.Basis ι (ZMod m) M.obj.obj.obj.V) (i : ℤ) :
    Subsingleton ((compactSupportSheafCohomology (ZMod m) f j kbar i).obj
      ((lisseEtaleSheaf B U x (ZMod m)).obj M)) := by
  let Λ := ZMod m
  obtain ⟨y, hy⟩ : ∃ y : GeometricPoint U.1, y.map g.hom = x := by
    let p' := (finiteEtaleFiberFunctor x).map ε.hom p₀
    refine ⟨⟨x.residueField, p'.1⟩, ?_⟩
    cases x
    simp only [GeometricPoint.map]
    congr 1
    exact p'.2
  subst hy
  let F := finiteEtaleFiberFunctor (y.map g.hom)
  let Y := F.obj (finiteEtaleOverSource hg)
  have : Finite Y := finite_finiteEtaleFiber _ _
  let : Fintype Y := Fintype.ofFinite _
  have : Nonempty Y := ⟨finiteEtaleOverSourcePoint hg y⟩
  have hY : ∀ z : Y, IsOpen (MulAction.stabilizer (EtaleFundamentalGroup U.1 (y.map g.hom)) z :
      Set (EtaleFundamentalGroup U.1 (y.map g.hom))) :=
    fun z => EtaleFundamentalGroup.isOpen_coe_of_isOpenSubgroup ⟨_, z, rfl⟩
  have hnat : ∀ {W W' : FiniteEtaleOver U.1} (φ : W ⟶ W')
      (σ : EtaleFundamentalGroup U.1 (y.map g.hom)) (z : F.obj W),
      F.map φ (σ • z) = σ • F.map φ z :=
    fun φ σ z => (ConcreteCategory.congr_hom (σ.asIso.hom.naturality φ) z).symm
  have hεε : ∀ z : Y, F.map ε.hom (F.map ε.inv z) = z := (F.mapIso ε).inv_hom_id_apply
  have hεε' : ∀ z : F.obj T.cover, F.map ε.inv (F.map ε.hom z) = z :=
    (F.mapIso ε).hom_inv_id_apply
  let τ' : K → Y → Y := fun a z => F.map ε.hom (F.map (T.τ a) (F.map ε.inv z))
  have hτ : ∀ (a : K) (σ : EtaleFundamentalGroup U.1 (y.map g.hom)) (z : Y),
      τ' a (σ • z) = σ • τ' a z := fun a σ z => by
    simp only [τ', hnat]
  have htr : ∀ z z' : Y, ∃! a : K, τ' a z = z' := fun z z' => by
    obtain ⟨a, ha, hu⟩ := T.existsUnique (y.map g.hom) (F.map ε.inv z) (F.map ε.inv z')
    refine ⟨a, ?_, fun b hb => hu b ?_⟩
    · show F.map ε.hom (F.map (T.τ a) (F.map ε.inv z)) = z'
      rw [ha, hεε]
    · change F.map ε.hom (F.map (T.τ b) (F.map ε.inv z)) = z' at hb
      rw [← hb, hεε']
  have hτadd : ∀ (a b : K) (z : Y), τ' (a + b) z = τ' a (τ' b z) := fun a b z => by
    simp only [τ', hεε', add_comm a b, T.τ_add, Functor.map_comp_apply]
  let κ := T.character (y.map g.hom) p₀
  have hκ : ∀ (σ : EtaleFundamentalGroup U.1 (y.map g.hom)) (z : Y),
      σ • z = τ' (Multiplicative.toAdd (κ σ)) z := fun σ z => by
    show σ • z = F.map ε.hom (F.map (T.τ _) (F.map ε.inv z))
    rw [← T.smul_eq_character (y.map g.hom) p₀ σ (F.map ε.inv z), hnat, hεε]
  let TF := lisseEtaleSheaf B U (y.map g.hom) Λ ⋙ compactSupportSheafCohomology Λ f j kbar i
  have : (lisseEtaleSheaf B U (y.map g.hom) Λ).Additive := by
    have : (finiteTypeLocallyConstantModuleSheafEquivalence B U (y.map g.hom) Λ).inverse.Additive :=
      Equivalence.additive_functor'
        (finiteTypeLocallyConstantModuleSheafEquivalence B U (y.map g.hom) Λ).symm
    have := Equivalence.additive_functor' (SmallEtale.sheafEquiv B U.1 U.2 (ModuleCat.{u + 1} Λ))
    dsimp only [lisseEtaleSheaf, lisseSheaf]
    infer_instance
  have : (compactSupportSheafCohomology Λ f j kbar i).Additive := by
    have := additive_liftSingle Λ U.1 (fun _ => ⟨0, inferInstance⟩)
    dsimp only [compactSupportSheafCohomology, sheafSingleComplex]
    infer_instance
  have : TF.Additive := inferInstanceAs (Functor.Additive (_ ⋙ _))
  obtain ⟨hfin, hcard⟩ := finite_and_natCard_permModule_eq_of_finiteEtale_endomorphism B U f j kbar
    m g hgf hg y hY i
  have : Finite (TF.obj (permModule m PUnit.{u + 2} hY)) := hfin
  exact subsingleton_obj_of_torsor_character m hY hK τ' hτ htr hτadd
    (finiteEtaleOverSourcePoint hg y) M ρ κ hκ hM bM hfix TF hcard

end Torsor

end Stacks.EtaleCohomology

/-! ### The Artin–Schreier cover of the affine line -/

namespace Stacks.ArtinSchreier

open Polynomial Stacks.EtaleCohomology

variable (k : Type u) [Field k] [Fintype k]

/-- `x ↦ x^q - x` on `k[x]`. -/
abbrev affineLineASMap : k[X] →ₐ[k] k[X] :=
  aeval ((Polynomial.X : k[X]) ^ Fintype.card k - Polynomial.X)

/-- `T^q - T - x` vanishes at `T = x` once its coefficients are mapped by `x ↦ x^q - x`. -/
theorem eval₂_poly_affineLineASMap :
    (poly k (Polynomial.X : k[X])).eval₂ (affineLineASMap k : k[X] →+* k[X]) Polynomial.X = 0 := by
  simp only [poly, eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_X, eval₂_C]
  show Polynomial.X ^ Fintype.card k - (Polynomial.X +
    aeval ((Polynomial.X : k[X]) ^ Fintype.card k - Polynomial.X) Polynomial.X) = 0
  rw [aeval_X]
  ring

/-- `root^q - root = x` in `k[x][T]/(T^q - T - x)`. -/
theorem root_pow_card_sub_root :
    AdjoinRoot.root (poly k (Polynomial.X : k[X])) ^ Fintype.card k -
        AdjoinRoot.root (poly k (Polynomial.X : k[X])) =
      AdjoinRoot.of (poly k (Polynomial.X : k[X])) Polynomial.X := by
  have h : AdjoinRoot.mk (poly k (Polynomial.X : k[X]))
      ((Polynomial.X : (k[X])[X]) ^ Fintype.card k - (Polynomial.X + C Polynomial.X)) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, map_add, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  linear_combination h

/-- **The Artin–Schreier cover of the affine line is an affine line**:
`k[x][T]/(T^q - T - x) ≅ k[T]`, `T ↦ T`, `x ↦ T^q - T`. -/
def affineLineRingEquiv : Ring k (Polynomial.X : k[X]) ≃ₐ[k] k[X] :=
  AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom _ (affineLineASMap k) Polynomial.X (eval₂_poly_affineLineASMap k))
    (aeval (AdjoinRoot.root (poly k (Polynomial.X : k[X]))))
    (by
      apply Polynomial.algHom_ext
      simp)
    (by
      apply AdjoinRoot.algHom_ext'
      · apply Polynomial.algHom_ext
        change (aeval (AdjoinRoot.root (poly k (Polynomial.X : k[X]))))
            ((AdjoinRoot.liftAlgHom _ (affineLineASMap k) Polynomial.X
              (eval₂_poly_affineLineASMap k)) (AdjoinRoot.of _ Polynomial.X)) =
          AdjoinRoot.of _ Polynomial.X
        rw [AdjoinRoot.liftAlgHom_of, affineLineASMap, aeval_X, map_sub, map_pow, aeval_X,
          root_pow_card_sub_root]
      · simp)

/-- The affine line `Spec k[x]` is the Artin–Schreier cover of itself. -/
def affineLineSpecIso : Spec (.of k[X]) ≅ Spec (.of (Ring k (Polynomial.X : k[X]))) where
  hom := Spec.map (CommRingCat.ofHom (affineLineRingEquiv k).toRingEquiv.toRingHom)
  inv := Spec.map (CommRingCat.ofHom (affineLineRingEquiv k).symm.toRingEquiv.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext fun x => (affineLineRingEquiv k).apply_symm_apply x
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext fun x => (affineLineRingEquiv k).symm_apply_apply x


section Vanishing

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- The structure morphism of the affine line. -/
abbrev affineLineStructureMap : Spec (.of k[X]) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k[X]))

/-- **The Artin–Schreier cover of the affine line, as an endomorphism of the affine line**,
`x ↦ x^q - x`, read through `Stacks.ArtinSchreier.affineLineSpecIso`. -/
abbrev affineLineASHom : Spec (.of k[X]) ⟶ Spec (.of k[X]) :=
  (affineLineSpecIso k).hom ≫ coverHom k k[X] Polynomial.X

/-- The endomorphism `x ↦ x^q - x` of the affine line lies over `Spec k`. -/
theorem affineLineASHom_comp_structureMap :
    affineLineASHom k ≫ affineLineStructureMap k = affineLineStructureMap k := by
  simp only [affineLineASHom, affineLineSpecIso, affineLineStructureMap, coverHom, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine RingHom.ext fun c => ?_
  show (affineLineRingEquiv k) (algebraMap k[X] (Ring k (Polynomial.X : k[X]))
    (algebraMap k k[X] c)) = algebraMap k k[X] c
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]

/-- The endomorphism `x ↦ x^q - x` of the affine line is finite étale. -/
theorem finiteEtale_affineLineASHom : finiteEtale (affineLineASHom k) :=
  ⟨inferInstanceAs (IsFinite (_ ≫ _)), inferInstanceAs (Etale (_ ≫ _))⟩

/-- The Artin–Schreier cover is isomorphic, over the affine line, to the endomorphism
`x ↦ x^q - x` of the affine line. -/
def coverIsoAffineLineASHom :
    cover k k[X] Polynomial.X ≅ finiteEtaleOverSource (finiteEtale_affineLineASHom k) :=
  MorphismProperty.Over.isoMk (affineLineSpecIso k).symm (by
    change (affineLineSpecIso k).inv ≫ (affineLineSpecIso k).hom ≫ coverHom k k[X] Polynomial.X =
      coverHom k k[X] Polynomial.X
    rw [Iso.inv_hom_id_assoc])


variable (B : BigEtaleSite.{u}) (hX : schemeSizeBelow B.cutoff (Spec (.of k[X])))
  [ConnectedSpace (Spec (.of k[X]))] {O : Type} [CommRing O] [IsDomain O] (ψ : AddChar k O)
  {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B (specObject k[X] B hX).1
    (specObject k[X] B hX).2) (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian (Spec (.of k[X]))]

/-- **`Hⁱ_c(𝔸¹_k̄, L_ψ) = 0`** for a nontrivial additive character `ψ` of `k`, at every finite
level: the levels of the Artin–Schreier sheaf `L_ψ(x)` on the affine line have no compactly
supported cohomology over `k̄`, through any compactification ([Laumon, 1.2.2.1]). Here `ℓ` is
different from the characteristic of `k`. -/
@[sga "4½ Sommes_trig 2.9" "special case"]
theorem subsingleton_compactSupportSheafCohomology_artinSchreierSheaf_etaleLevel (hψ : ψ ≠ 1)
    (hℓ : ℓ ≠ ringChar k) (x : GeometricPoint (Spec (.of k[X])))
    (p₀ : (finiteEtaleFiberFunctor x).obj (cover k k[X] Polynomial.X))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) (kbar : Type u) [Field kbar]
    [Algebra k kbar] [IsAlgClosed kbar] (n : ℕ) (i : ℤ) :
    Subsingleton ((compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) (affineLineStructureMap k) j
      kbar i).obj (LAdicSheaf.etaleLevel B (specObject k[X] B hX) ℓ
        (artinSchreierSheaf k k[X] Polynomial.X ψ B hX b x p₀).toLAdicSheaf n)) := by
  let pU := affineLineStructureMap k
  let U := specObject k[X] B hX
  let Λ := ZMod (ℓ ^ (n + 1))
  have : IsCurve k pU := isCurve_specPolynomial k
  have : LocallyOfFiniteType pU := locallyOfFiniteType_specPolynomial k
  have : Algebra.Smooth k k[X] := {}
  have : Smooth pU := smooth_Spec_map_algebraMap k k[X]
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let g : U ⟶ U := ObjectProperty.homMk (affineLineASHom k)
  have : IsFinite (B.inclusion.map g) := inferInstanceAs (IsFinite (affineLineASHom k))
  have : Etale (B.inclusion.map g) := inferInstanceAs (Etale (affineLineASHom k))
  have hgf : g.hom ≫ pU = pU := affineLineASHom_comp_structureMap k
  have hK : IsUnit (Fintype.card k : Λ) := by
    obtain ⟨r, hp, hr⟩ := FiniteField.card k (ringChar k)
    rw [ZMod.isUnit_iff_coprime, hr]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp (Fact.out : ℓ.Prime)).2 (Ne.symm hℓ))
  let ρ := characterRepresentation B U x b (artinSchreierCharacter k k[X] Polynomial.X ψ x p₀)
  let hρ := continuous_artinSchreierRepresentation k k[X] Polynomial.X ψ B hX b x p₀
  rw [show LAdicSheaf.etaleLevel B U ℓ
      (artinSchreierSheaf k k[X] Polynomial.X ψ B hX b x p₀).toLAdicSheaf n
      = (lisseEtaleSheaf B U x Λ).obj (levelModule ρ hρ (n + 1)) from
    (congrArg (SmallEtale.sheafEquiv B U.1 U.2 (ModuleCat.{u + 1} Λ)).functor.obj
      (lisseSheaf_obj_levelModule B U x ρ hρ (n + 1))).symm]
  let L : ULift.{u + 1} (Fin d → Λ) ≃ₗ[Λ] (Fin d → Λ) := ULift.moduleEquiv
  let R : Multiplicative k →* GL (Fin d) ℤ_[ℓ] :=
    (Units.map (Algebra.leftMulMatrix b).toMonoidHom).comp
      (ψ.toMonoidHom.toHomUnits.comp invMonoidHom)
  let A : Multiplicative k → Matrix (Fin d) (Fin d) Λ :=
    fun a => (R a).val.map (PadicInt.toZModPow (n + 1))
  have hA1 : A 1 = 1 := by
    simp only [A, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hAmul : ∀ a a', A (a * a') = A a * A a' := fun a a' => by
    simp only [A, map_mul, Units.val_mul]
    exact Matrix.map_mul
  let ρK : Multiplicative k →* Module.End Λ (ULift.{u + 1} (Fin d → Λ)) :=
    { toFun := fun a => L.symm.toLinearMap ∘ₗ Matrix.toLin' (A a) ∘ₗ L.toLinearMap
      map_one' := by
        ext v : 1
        apply ULift.ext
        simp [hA1, L]
      map_mul' := fun a a' => by
        ext v : 1
        apply ULift.ext
        simp [hAmul, L, Module.End.mul_apply] }
  have hM : ∀ (σ : EtaleFundamentalGroup U.1 x) (v : ULift.{u + 1} (Fin d → Λ)),
      ((levelModule ρ hρ (n + 1)).obj.obj.obj.ρ σ).asHom.hom v =
        ρK ((torsorCover k k[X] Polynomial.X).character x p₀ σ) v := fun σ v => rfl
  have hsum : ∑ a : k, A (Multiplicative.ofAdd a) = 0 := by
    have h1 : ∀ a : k, (R (Multiplicative.ofAdd a)).val = Algebra.leftMulMatrix b (ψ (-a)) :=
      fun a => rfl
    have h2 : ∑ a : k, ψ (-a) = 0 := by
      rw [show (∑ a : k, ψ (-a)) = ∑ a : k, ψ a from
        Fintype.sum_equiv (Equiv.neg k) _ _ fun _ => rfl]
      exact AddChar.sum_eq_zero_of_ne_one hψ
    have h3 : ∀ a : k, A (Multiplicative.ofAdd a) =
        (PadicInt.toZModPow (n + 1)).mapMatrix (Algebra.leftMulMatrix b (ψ (-a))) := fun a => by
      simp only [A, h1]
      rfl
    simp only [h3]
    rw [← map_sum, ← map_sum, h2, map_zero, map_zero]
  have hfix : ∀ v, ∑ a : k, ρK (Multiplicative.ofAdd a) v = 0 := fun v => by
    show ∑ a : k, L.symm (Matrix.toLin' (A (Multiplicative.ofAdd a)) (L v)) = 0
    simp only [Matrix.toLin'_apply]
    rw [← map_sum, ← Matrix.sum_mulVec, hsum, Matrix.zero_mulVec, map_zero]
  let bM : Module.Basis (ULift.{u + 1} (Fin d)) Λ (ULift.{u + 1} (Fin d → Λ)) :=
    ((Pi.basisFun Λ (Fin d)).map L.symm).reindex Equiv.ulift.symm
  exact subsingleton_compactSupportSheafCohomology_of_torsor_character B U pU j kbar (ℓ ^ (n + 1))
    g hgf (finiteEtale_affineLineASHom k) hK (torsorCover k k[X] Polynomial.X)
    (coverIsoAffineLineASHom k) x p₀ (levelModule ρ hρ (n + 1)) ρK hM hfix bM i

end Vanishing

end Stacks.ArtinSchreier
