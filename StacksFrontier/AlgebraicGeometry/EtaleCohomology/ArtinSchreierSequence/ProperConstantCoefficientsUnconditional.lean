module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
public import StacksFrontier.Topology.Spectral.ConstructibleTopology
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperConstantCoefficients
import all
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperConstantCoefficients

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusFixedPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.TopDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.TopDegreeVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# Étale cohomology with constant coefficients `𝐙/p𝐙` of a proper scheme, unconditionally

Let `X` be proper over an algebraically closed field `k` of characteristic `p > 0`. Then every
étale cohomology group `H ^ q (X_étale, 𝐙/p𝐙)` is finite, and restriction to the scalar extension
`X_{k'}` along an extension `k'/k` of algebraically closed fields is bijective on it. Unlike in
`ProperConstantCoefficients`, the Artin–Schreier sequence and the comparison of étale with
Zariski cohomology of the structure sheaf are not hypotheses.

## Main results

* `Stacks.ArtinSchreier.finite_etaleH_constantZMod_of_isProper_unconditional`:
  `H ^ q (X_étale, 𝐙/p𝐙)` is finite.
* `Stacks.ArtinSchreier.bijective_etaleCohomologyBaseChangeMap_constantZMod`: restriction
  `H ^ q (X_étale, 𝐙/p𝐙) ⟶ H ^ q (X_{k'}, 𝐙/p𝐙)` is bijective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w u

namespace Stacks.ArtinSchreier

section ConstantCoefficients

/-- **Conjugating a Frobenius-semilinear map by an additive bijection.** If `E : W ≃+ V` carries
the scalar `a` to `S a` and `Φ ∘ S a = S (a ^ p) ∘ Φ`, then `E⁻¹ ∘ Φ ∘ E` is `p`-semilinear. -/
private theorem conj_frobenius_semilinear_of_addEquiv {p : ℕ} {k : Type*} [Semiring k]
    {W V : Type*} [AddCommMonoid W] [Module k W] [AddCommMonoid V] (E : W ≃+ V) (Φ : V →+ V)
    (S : k → V →+ V) (hE : ∀ (a : k) (w : W), E (a • w) = S a (E w))
    (hΦ : ∀ (a : k) (v : V), Φ (S a v) = S (a ^ p) (Φ v)) (a : k) (w : W) :
    (E.symm.toAddMonoidHom.comp (Φ.comp E.toAddMonoidHom)) (a • w) =
      a ^ p • (E.symm.toAddMonoidHom.comp (Φ.comp E.toAddMonoidHom)) w := by
  apply E.injective
  simp [hE, hΦ]

/-- **The Frobenius-fixed vectors of a finite-dimensional space, read through an additive
bijection, are finite.** Let `W` be a finite-dimensional vector space over a field `k` of
characteristic `p > 0` and `E : W ≃+ V` an additive bijection carrying the scalar `a` to an
additive endomorphism `S a` of `V`. If `Φ` is an additive endomorphism of `V` with
`Φ ∘ S a = S (a ^ p) ∘ Φ`, then the vectors of `V` fixed by `Φ` form a finite set. -/
public theorem finite_fixedPoints_of_addEquiv {p : ℕ} [Fact p.Prime] (k : Type*) [Field k]
    [CharP k p] {W V : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V] (E : W ≃+ V) (Φ : V →+ V) (S : k → V →+ V)
    (hE : ∀ (a : k) (w : W), E (a • w) = S a (E w))
    (hΦ : ∀ (a : k) (v : V), Φ (S a v) = S (a ^ p) (Φ v)) :
    Finite {v : V // Φ v = v} := by
  let F : W →+ W := E.symm.toAddMonoidHom.comp (Φ.comp E.toAddMonoidHom)
  have hF : ∀ (a : k) (w : W), F (a • w) = a ^ p • F w :=
    conj_frobenius_semilinear_of_addEquiv E Φ S hE hΦ
  let : Module (ZMod p) W := Module.compHom W (ZMod.castHom (dvd_refl p) k)
  have := fixedPoints_finiteDimensional_of_frobenius_semilinear p k W F hF
  have : Finite (AddMonoidHom.ker (F - AddMonoidHom.id W)) := Module.finite_of_finite (ZMod p)
  refine Finite.of_injective (fun v : {v : V // Φ v = v} =>
    (⟨E.symm v.1, ?_⟩ : AddMonoidHom.ker (F - AddMonoidHom.id W)))
    fun a b hab => Subtype.ext (E.symm.injective (congrArg Subtype.val hab))
  simp [F, v.2]

variable {p : ℕ} (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (hX : (p : Γ(X, ⊤)) = 0)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The Frobenius on the cohomology of `𝐆_a` is semilinear over `k`**: it carries
multiplication by `a ∈ k` to multiplication by `a ^ p`. -/
private theorem sheafH_map_frobeniusMap_scalarMap (hp : p.Prime) (q : ℕ) (a : k)
    (y : Sheaf.H.{w} (additiveSheaf.{u, 0} X) q) :
    Sheaf.H.map (frobeniusMap.{u, 0} X hp hX) q
        (Sheaf.H.map (scalarMap.{u, 0} X (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a)) q y) =
      Sheaf.H.map (scalarMap.{u, 0} X (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) (a ^ p))) q
        (Sheaf.H.map (frobeniusMap.{u, 0} X hp hX) q y) := by
  rw [← Sheaf.H.map_comp_apply, scalarMap_comp_frobeniusMap, Sheaf.H.map_comp_apply, map_pow]

/-- **The inclusion of `𝐙/p𝐙` in `𝐆_a` is injective on cohomology.** Let `X` be a scheme over an
algebraically closed field `k` of characteristic `p > 0`. If `H ^ (q - 1) (X, 𝒪_X)` is a
finite-dimensional `k`-vector space (no condition when `q = 0`), the map
`H ^ q (X_étale, 𝐙/p𝐙) ⟶ H ^ q (X_étale, 𝐆_a)` is injective. -/
@[sga "4 XVII 5.5.35" "Injectivity of H^q(X"]
public theorem injective_sheafH_map_zmodSheafHom (hp : p.Prime) [IsAlgClosed k] [CharP k p]
    (q : ℕ)
    (hfin : ∀ i : ℕ, i + 1 = q → FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) i)) :
    Function.Injective (Sheaf.H.map.{w} (zmodSheafHom.{u, 0} X hX) q) := by
  have hS := constantArtinSchreierSequence_shortExact.{u, 0} X hp hX
  rw [injective_iff_map_eq_zero]
  intro x hx
  cases q with
  | zero =>
    have : Mono (zmodSheafHom.{u, 0} X hX) := hS.mono_f
    exact (injective_iff_map_eq_zero ((Ext.mk₀ (zmodSheafHom.{u, 0} X hX)).postcomp _
      (add_zero 0))).mp (Ext.postcomp_mk₀_injective_of_mono _ _) x hx
  | succ q' =>
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hS x hx rfl
    obtain ⟨x₂, rfl⟩ := surjective_sheafH_map_artinSchreierMap.{u, 0, w} hp k f hX q'
      (hfin q' rfl) x₃
    rw [← hx₃]
    exact (Ext.comp_assoc_of_second_deg_zero
      (Y := (constantArtinSchreierSequence.{u, 0} X hp hX).X₂)
      (Z := (constantArtinSchreierSequence.{u, 0} X hp hX).X₃) x₂
      (Ext.mk₀ (constantArtinSchreierSequence.{u, 0} X hp hX).g) hS.extClass rfl).trans
      (by rw [hS.comp_extClass]; apply Ext.comp_zero)

/-- A class of `H ^ q (X_étale, 𝐆_a)` is killed by `F - 1` iff it is fixed by the Frobenius. -/
private theorem sheafH_map_artinSchreierMap_eq_zero_iff (hp : p.Prime) (q : ℕ)
    (y : Sheaf.H.{w} (additiveSheaf.{u, 0} X) q) :
    Sheaf.H.map (artinSchreierMap.{u, 0} X hp hX) q y = 0 ↔
      Sheaf.H.map (frobeniusMap.{u, 0} X hp hX) q y = y := by
  rw [artinSchreierMap, Sheaf.H.map_sub_apply, Sheaf.H.map_id_apply, sub_eq_zero]

/-- **The image of `𝐙/p𝐙` on cohomology is fixed by the Frobenius**: the composite of the
inclusion of `𝐙/p𝐙` with the Artin–Schreier map `F - 1` is zero. -/
public theorem sheafH_map_frobeniusMap_zmodSheafHom (hp : p.Prime) (q : ℕ)
    (x : Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) :
    Sheaf.H.map (frobeniusMap.{u, 0} X hp hX) q (Sheaf.H.map (zmodSheafHom.{u, 0} X hX) q x) =
      Sheaf.H.map (zmodSheafHom.{u, 0} X hX) q x := by
  have hz : Sheaf.H.map (artinSchreierMap.{u, 0} X hp hX) q
      (Sheaf.H.map (zmodSheafHom.{u, 0} X hX) q x) = 0 := by
    rw [← Sheaf.H.map_comp_apply, zmodSheafHom_comp_artinSchreierMap, Sheaf.H.map_apply,
      Ext.mk₀_zero, Ext.comp_zero]
  exact (sheafH_map_artinSchreierMap_eq_zero_iff hX hp q _).mp hz

/-- **Every Frobenius-fixed class of `𝐆_a` comes from `𝐙/p𝐙`**: a class of
`H ^ q (X_étale, 𝐆_a)` fixed by the Frobenius is the image of a class of
`H ^ q (X_étale, 𝐙/p𝐙)`. -/
@[sga "4 XVII 5.5.35" "partial", sga "4½ Fonctions_L 3.6" "partial"]
public theorem exists_sheafH_map_zmodSheafHom_eq (hp : p.Prime) (q : ℕ)
    (y : Sheaf.H.{w} (additiveSheaf.{u, 0} X) q)
    (hy : Sheaf.H.map (frobeniusMap.{u, 0} X hp hX) q y = y) :
    ∃ x : Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q,
      Sheaf.H.map (zmodSheafHom.{u, 0} X hX) q x = y := by
  exact Ext.covariant_sequence_exact₂ _ (constantArtinSchreierSequence_shortExact.{u, 0} X hp hX)
    y ((sheafH_map_artinSchreierMap_eq_zero_iff hX hp q y).mpr hy)

/-- Let `X` be a scheme proper over an algebraically closed field `k` of characteristic `p > 0`.
Then `H ^ q (X_étale, 𝐙/p𝐙)` is finite for every `q`. -/
@[stacks 0A3P "(1)"]
public theorem finite_etaleH_constantZMod_of_isProper_unconditional (hp : 0 < p) [IsAlgClosed k]
    [CharP k p] [IsProper f] (q : ℕ) :
    Finite (Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) := by
  have : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have hpp : p.Prime := Fact.out
  have hX : (p : Γ(X, ⊤)) = 0 := natCast_eq_zero_of_charP k p f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hfin : ∀ i : ℕ, FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) i) := fun i =>
    finiteDimensional_cohomologyOverField_of_isProper k f (SheafOfModules.unit X.ringCatSheaf) i
  obtain ⟨E, hE⟩ := exists_addEquiv_cohomologyOverField_sheafH.{u, 0, w} k f q
  have := hfin q
  have hfix : Finite {y : Sheaf.H.{w} (additiveSheaf.{u, 0} X) q //
      Sheaf.H.map (frobeniusMap.{u, 0} X hpp hX) q y = y} :=
    finite_fixedPoints_of_addEquiv k E _ (fun a => Sheaf.H.map (scalarMap.{u, 0} X
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a)) q) hE
      (sheafH_map_frobeniusMap_scalarMap k f hX hpp q)
  exact Finite.of_injective (fun x => (⟨_, sheafH_map_frobeniusMap_zmodSheafHom hX hpp q x⟩ :
    {y : Sheaf.H.{w} (additiveSheaf.{u, 0} X) q //
      Sheaf.H.map (frobeniusMap.{u, 0} X hpp hX) q y = y})) fun a b hab =>
    injective_sheafH_map_zmodSheafHom k f hX hpp q (fun i _ => hfin i) (congrArg Subtype.val hab)

end ConstantCoefficients

section FixedVectors

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- **An additive bijection onto a space spanned additively by scalar multiples.** Let
`E' : W' ≃+ V'` carry the scalar `a ∈ k'` to `S' a`, and let `R : V →+ V'` be additive. If the
multiples `S' c (R z)` generate `V'` as an additive group, then the image of `E'⁻¹ ∘ R ∘ E`
spans `W'` over `k'`. -/
private theorem span_range_eq_top_of_mem_closure {k' : Type*} [Ring k'] {W W' V V' : Type*}
    [AddCommGroup W] [AddCommGroup W'] [Module k' W'] [AddCommGroup V] [AddCommGroup V']
    (E : W ≃+ V) (E' : W' ≃+ V') (R : V →+ V') (S' : k' → V' →+ V')
    (hS' : ∀ (a : k') (y : V'), E'.symm (S' a y) = a • E'.symm y)
    (hspan : ∀ y, y ∈ AddSubgroup.closure (Set.range fun cz : k' × V => S' cz.1 (R cz.2))) :
    Submodule.span k' (Set.range (E'.symm.toAddMonoidHom.comp (R.comp E.toAddMonoidHom))) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have key : ∀ y ∈ AddSubgroup.closure (Set.range fun cz : k' × V => S' cz.1 (R cz.2)),
      E'.symm y ∈
        Submodule.span k' (Set.range (E'.symm.toAddMonoidHom.comp (R.comp E.toAddMonoidHom))) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨c, z⟩, rfl⟩ := hy
      rw [hS']
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨E.symm z, by simp⟩)
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
    | neg y _ hy =>
      rw [map_neg]
      exact Submodule.neg_mem _ hy
  simpa only [AddEquiv.symm_apply_apply] using key (E' v) (hspan (E' v))

/-- **Frobenius-fixed vectors lift along a base change read through additive bijections.** Let
`W` be finite-dimensional over an algebraically closed field `k` and `W'` a vector space over an
algebraically closed extension `k'`, both of characteristic `p > 0`, read through additive
bijections `E : W ≃+ V` and `E' : W' ≃+ V'` that carry scalars to `S a` and `S' a`. Let `Φ`, `Φ'`
be `p`-semilinear additive endomorphisms and `R : V →+ V'` an injective, `φ`-semilinear map
intertwining them whose image generates `V'` additively over `k'`. Then every `Φ'`-fixed vector
of `V'` is the image under `R` of a `Φ`-fixed vector of `V`. -/
private theorem exists_fixedPoint_of_addEquiv {p : ℕ} (hp : 0 < p)
    {k k' : Type*} [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k']
    [CharP k p] [CharP k' p] (φ : k →+* k')
    {W W' V V' : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup W'] [Module k' W'] [AddCommGroup V] [AddCommGroup V']
    (E : W ≃+ V) (E' : W' ≃+ V') (S : k → V →+ V) (S' : k' → V' →+ V')
    (hE : ∀ (a : k) (w : W), E (a • w) = S a (E w))
    (hE' : ∀ (a : k') (w : W'), E' (a • w) = S' a (E' w))
    (Φ : V →+ V) (Φ' : V' →+ V')
    (hΦ : ∀ (a : k) (v : V), Φ (S a v) = S (a ^ p) (Φ v))
    (hΦ' : ∀ (a : k') (v : V'), Φ' (S' a v) = S' (a ^ p) (Φ' v))
    (R : V →+ V') (hR : ∀ (a : k) (v : V), R (S a v) = S' (φ a) (R v))
    (hRΦ : ∀ v, R (Φ v) = Φ' (R v)) (hinj : Function.Injective R)
    (hspan : ∀ y, y ∈ AddSubgroup.closure (Set.range fun cz : k' × V => S' cz.1 (R cz.2)))
    (w : V') (hw : Φ' w = w) : ∃ v, Φ v = v ∧ R v = w := by
  let F := E.symm.toAddMonoidHom.comp (Φ.comp E.toAddMonoidHom)
  let F' := E'.symm.toAddMonoidHom.comp (Φ'.comp E'.toAddMonoidHom)
  have hS' : ∀ (a : k') (y : V'), E'.symm (S' a y) = a • E'.symm y := by
    intro a y
    apply E'.injective
    rw [hE', AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hbij := bijOn_fixedPoints_of_frobenius_base_change hp φ F
    (conj_frobenius_semilinear_of_addEquiv E Φ S hE hΦ) F'
    (conj_frobenius_semilinear_of_addEquiv E' Φ' S' hE' hΦ')
    (E'.symm.toAddMonoidHom.comp (R.comp E.toAddMonoidHom)) (fun a v => by simp [hE, hR, hS'])
    (E'.symm.injective.comp (hinj.comp E.injective))
    (span_range_eq_top_of_mem_closure E E' R S' hS' hspan) (fun v => by simp [F, F', hRΦ])
  obtain ⟨v, hv : E.symm (Φ (E v)) = v, hvβ : E'.symm (R (E v)) = E'.symm w⟩ :=
    hbij.surjOn (show F' (E'.symm w) = E'.symm w by simp [F', hw])
  exact ⟨E v, E.symm.injective (hv.trans (E.symm_apply_apply v).symm), E'.symm.injective hvβ⟩

end FixedVectors

section BaseChange

open Stacks.EtaleCohomology

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- **The pullback of a scalar to the scalar extension.** For `X` over `k` and a field extension
`k'/k`, pulling the image of `a ∈ k` in `Γ(X, 𝒪_X)` back to `X_{k'}` gives the image of `a ∈ k'`
in `Γ(X_{k'}, 𝒪)`, the scalar extension being a scheme over `k'` through its second
projection. -/
public theorem scalarExtensionFst_appTop_algebraMap (a : k) :
    (scalarExtensionFst k k' f).appTop (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a) =
      ((Scheme.ΓSpecIso (.of k')).inv ≫
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop)
        (algebraMap k k' a) := by
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k k'))) a
  simp only [ConcreteCategory.comp_apply] at hn ⊢
  rw [← ConcreteCategory.comp_apply f.appTop, ← Scheme.Hom.comp_appTop, pullback.condition,
    Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ← hn]
  rfl

/-- Let `X` be proper over an algebraically closed field `k` of characteristic `p > 0`, and let
`k'/k` be an extension of algebraically closed fields. Then the restriction map
`H ^ q (X_étale, 𝐙/p𝐙) ⟶ H ^ q (X_{k'}, 𝐙/p𝐙)` to the scalar extension
`X_{k'} = X ×_{Spec k} Spec k'` is bijective. -/
@[stacks 0A3P "(2)"]
public theorem bijective_etaleCohomologyBaseChangeMap_constantZMod {p : ℕ} (hp : 0 < p)
    [IsAlgClosed k] [IsAlgClosed k'] [CharP k p] [IsProper f]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) :
    Function.Bijective
      (etaleCohomologyBaseChangeMap.{u, 0, w} k k' f (etaleConstantZMod X p) q) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨hinj, hspan⟩ := additiveCohomologyRestriction_scalarExtension.{w} k k' f q
  set f' := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) with hf'
  set π := scalarExtensionFst k k' f
  have : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have hpp : p.Prime := Fact.out
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have hX : (p : Γ(X, ⊤)) = 0 := natCast_eq_zero_of_charP k p f
  have hX' : (p : Γ(scalarExtension k k' f, ⊤)) = 0 := natCast_eq_zero_of_charP k' p f'
  have : IsProper f' := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian (scalarExtension k k' f) := LocallyOfFiniteType.isLocallyNoetherian f'
  have hfin := finiteDimensional_cohomologyOverField_of_isProper k f
    (SheafOfModules.unit X.ringCatSheaf)
  have hfin' := finiteDimensional_cohomologyOverField_of_isProper k' f'
    (SheafOfModules.unit (scalarExtension k k' f).ringCatSheaf)
  have := hfin q
  obtain ⟨E, hE⟩ := exists_addEquiv_cohomologyOverField_sheafH.{u, 0, w} k f q
  obtain ⟨E', hE'⟩ := exists_addEquiv_cohomologyOverField_sheafH.{u, 0, w} k' f' q
  let R := additiveCohomologyRestriction.{u, 0, w} π q
  have hfix := exists_fixedPoint_of_addEquiv hp (algebraMap k k') E E'
    (fun a => Sheaf.H.map (scalarMap.{u, 0} X (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) a)) q)
    (fun a => Sheaf.H.map (scalarMap.{u, 0} (scalarExtension k k' f)
      (((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop) a)) q) hE hE' _ _
    (sheafH_map_frobeniusMap_scalarMap k f hX hpp q)
    (sheafH_map_frobeniusMap_scalarMap (X := scalarExtension k k' f) k' f' hX' hpp q) R
    (fun a v => by
      rw [additiveCohomologyRestriction_sheafH_map_scalarMap, scalarExtensionFst_appTop_algebraMap,
        ← hf'])
    (additiveCohomologyRestriction_sheafH_map_frobeniusMap _ hpp hX hX' q) hinj hspan
  let A := AddCommGrpCat.of (ULift.{u + 1} (ZMod p))
  let eH := Sheaf.H.map.{w} ((etaleAbelianInverseImageConstantIso.{u, 0} π).hom.app A) q
  have heH : Function.Injective eH := by
    intro a b hab
    have h := congrArg (Sheaf.H.map.{w}
      ((etaleAbelianInverseImageConstantIso.{u, 0} π).inv.app A) q) hab
    simpa only [eH, ← Sheaf.H.map_comp_apply, Iso.hom_inv_id_app, Sheaf.H.map_id_apply] using h
  have hladder : ∀ x, Sheaf.H.map (zmodSheafHom.{u, 0} (scalarExtension k k' f) hX') q
      (eH (etaleCohomologyBaseChangeMap.{u, 0, w} k k' f (etaleConstantZMod X p) q x)) =
        R (Sheaf.H.map (zmodSheafHom.{u, 0} X hX) q x) := fun x =>
    (additiveCohomologyRestriction_sheafH_map_zmodSheafHom π hX hX' q x).symm
  refine ⟨fun a b hab => ?_, fun z => ?_⟩
  · refine injective_sheafH_map_zmodSheafHom k f hX hpp q (fun i _ => hfin i) (hinj ?_)
    rw [← hladder, ← hladder, hab]
  · obtain ⟨v, hv, hvR⟩ := hfix _ (sheafH_map_frobeniusMap_zmodSheafHom hX' hpp q (eH z))
    obtain ⟨x, hx⟩ := exists_sheafH_map_zmodSheafHom_eq hX hpp q v hv
    exact ⟨x, heH (injective_sheafH_map_zmodSheafHom k' f' hX' hpp q (fun i _ => hfin' i)
      ((hladder x).trans ((congrArg R hx).trans hvR)))⟩

end BaseChange

end Stacks.ArtinSchreier

end
