module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.AffineBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusChainAssembly
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFibreEuler

/-!
# The Riemann–Hurwitz formula for a Galois finite étale cover of a curve

Let `X` be a smooth, proper, geometrically irreducible curve over a field `k` and `Z ⟶ X` a Galois
finite étale cover of degree `d` such that `Z` is again a smooth, proper, geometrically
irreducible curve over `k`. Then

`g_Z - 1 = d (g_X - 1)`.

This is the formula `2 g_Y - 2 = (#G)(2 g_X - 2)` used in the proof of Stacks Tag 03W5.

## The proof

The fibre product `W = Z ×_X Z` of a Galois cover with itself is the disjoint union of the graphs
`s_τ = (𝟙, τ) : Z ⟶ W`, `τ ∈ Aut Z`: two morphisms into a Galois cover differ, near every point,
by an automorphism (`AlgebraicGeometry.exists_aut_mem_agreeLocus`), and an automorphism of a
connected cover is determined by one composite (`AlgebraicGeometry.aut_eq_of_comp_eq`). Each
`s_τ` is a section of the étale separated projection `W ⟶ Z`, hence an open and finite immersion.
So `h^n(W, 𝒪) = #Aut(Z) · h^n(Z, 𝒪)` for every `n`, and `#Aut(Z) = d`.

Let `π : Z ⟶ X` and `ℰ = π_* 𝒪_Z`, finite locally free of rank `d`. By affine base change,
`π^* ℰ ≅ pr_{1*} 𝒪_W`, so `χ(Z, π^* ℰ) = χ(W, 𝒪_W) = d χ(Z, 𝒪_Z)`, that is, `π^* ℰ` has degree
zero. By Stacks Tag 0AYZ, `deg(π^* ℰ) = deg(π) · deg(ℰ)` with `deg(π) = d > 0`, so `ℰ` has degree
zero: `χ(Z, 𝒪_Z) = χ(X, ℰ) = d χ(X, 𝒪_X)`. Finally `χ(𝒪) = 1 - g` on a geometrically integral
proper curve.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_pullback_self`: `h^n(W, 𝒪) = #Aut(Z) h^n(Z, 𝒪)`.
* `AlgebraicGeometry.genus_sub_one_eq_of_isGalois`: the Riemann–Hurwitz formula.
-/

@[expose] public noncomputable section

open CategoryTheory Limits PreGaloisCategory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X] (Z : FiniteEtaleOver X)

/-- The graph `(𝟙, τ) : Z ⟶ Z ×_X Z` of an automorphism `τ` of a finite étale cover. -/
def finiteEtaleAutGraph (τ : Aut Z) : Z.left ⟶ pullback Z.hom Z.hom :=
  pullback.lift (𝟙 _) τ.asIso.hom.left (by rw [Category.id_comp, MorphismProperty.Over.w])

omit [ConnectedSpace X] in
/-- The first projection of the graph of an automorphism is the identity. -/
@[reassoc (attr := simp)]
theorem finiteEtaleAutGraph_fst (τ : Aut Z) :
    finiteEtaleAutGraph Z τ ≫ pullback.fst Z.hom Z.hom = 𝟙 _ :=
  pullback.lift_fst _ _ _

omit [ConnectedSpace X] in
/-- The second projection of the graph of an automorphism `τ` is `τ`. -/
@[reassoc (attr := simp)]
theorem finiteEtaleAutGraph_snd (τ : Aut Z) :
    finiteEtaleAutGraph Z τ ≫ pullback.snd Z.hom Z.hom = τ.asIso.hom.left :=
  pullback.lift_snd _ _ _

/-- The graph of an automorphism of a finite étale cover is a finite morphism. -/
instance (τ : Aut Z) : IsFinite (finiteEtaleAutGraph Z τ) := by
  have : IsFinite Z.hom := Z.prop.1
  exact MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) _
    (pullback.fst Z.hom Z.hom) inferInstance (by rw [finiteEtaleAutGraph_fst]; infer_instance)

/-- The graph of an automorphism of a finite étale cover is an open immersion. -/
instance (τ : Aut Z) : IsOpenImmersion (finiteEtaleAutGraph Z τ) := by
  have : Etale Z.hom := Z.prop.2
  have h : finiteEtaleAutGraph Z τ ≫ pullback.fst Z.hom Z.hom = 𝟙 _ := finiteEtaleAutGraph_fst Z τ
  have : Etale (finiteEtaleAutGraph Z τ) :=
    MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ (pullback.fst Z.hom Z.hom)
      inferInstance (by rw [h]; infer_instance)
  have : Mono (finiteEtaleAutGraph Z τ) := mono_of_mono_fac h
  exact isOpenImmersion_of_etale_universallyInjective _

variable [IsGalois Z]

/-- The graphs of the automorphisms of a Galois cover cover `Z ×_X Z`. -/
theorem exists_finiteEtaleAutGraph_apply (w : ↥(pullback Z.hom Z.hom)) :
    ∃ (τ : Aut Z) (z : Z.left), (finiteEtaleAutGraph Z τ).base z = w := by
  obtain ⟨τ, h, hw⟩ := exists_aut_mem_agreeLocus (pullback.fst Z.hom Z.hom)
    (pullback.snd Z.hom Z.hom) pullback.condition w
  set L := Scheme.Hom.agreeLocus Z.hom (pullback.fst Z.hom Z.hom ≫ τ.asIso.hom.left)
    (pullback.snd Z.hom Z.hom) h
  have hL := Scheme.Hom.agreeLocus_ι_comp Z.hom (pullback.fst Z.hom Z.hom ≫ τ.asIso.hom.left)
    (pullback.snd Z.hom Z.hom) h
  have hfac : L.ι = (L.ι ≫ pullback.fst Z.hom Z.hom) ≫ finiteEtaleAutGraph Z τ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, finiteEtaleAutGraph_fst]
      exact (Category.comp_id _).symm
    · rw [Category.assoc, Category.assoc, finiteEtaleAutGraph_snd]
      exact hL.symm
  refine ⟨τ, (pullback.fst Z.hom Z.hom).base w, ?_⟩
  have := congrArg (fun φ : L.toScheme ⟶ _ => φ.base ⟨w, hw⟩) hfac
  simp only [Scheme.Hom.comp_base, Scheme.Opens.ι_apply] at this
  exact this.symm

/-- The graphs of distinct automorphisms of a Galois cover are disjoint. -/
theorem disjoint_range_finiteEtaleAutGraph :
    Pairwise fun τ τ' : Aut Z =>
      Disjoint (Set.range (finiteEtaleAutGraph Z τ).base)
        (Set.range (finiteEtaleAutGraph Z τ').base) := by
  intro τ τ' hne
  rw [Set.disjoint_left]
  rintro w ⟨z, rfl⟩ ⟨z', hz'⟩
  have h1 : ∀ σ : Aut Z, (pullback.fst Z.hom Z.hom ≫ σ.asIso.hom.left) ≫ Z.hom =
      pullback.snd Z.hom Z.hom ≫ Z.hom := fun σ => by
    rw [Category.assoc, MorphismProperty.Over.w, pullback.condition]
  have hmem : ∀ (σ : Aut Z) (y : Z.left), (finiteEtaleAutGraph Z σ).base y ∈
      Scheme.Hom.agreeLocus Z.hom (pullback.fst Z.hom Z.hom ≫ σ.asIso.hom.left)
        (pullback.snd Z.hom Z.hom) (h1 σ) := fun σ y =>
    Scheme.Hom.mem_agreeLocus_of_comp_eq Z.hom _ _ (h1 σ) (finiteEtaleAutGraph Z σ)
      (by rw [finiteEtaleAutGraph_fst_assoc, finiteEtaleAutGraph_snd]) y
  set Lτ := Scheme.Hom.agreeLocus Z.hom (pullback.fst Z.hom Z.hom ≫ τ.asIso.hom.left)
    (pullback.snd Z.hom Z.hom) (h1 τ)
  set Lτ' := Scheme.Hom.agreeLocus Z.hom (pullback.fst Z.hom Z.hom ≫ τ'.asIso.hom.left)
    (pullback.snd Z.hom Z.hom) (h1 τ')
  have hwτ' : (finiteEtaleAutGraph Z τ).base z ∈ Lτ' := by rw [← hz']; exact hmem τ' z'
  have : Nonempty (Lτ ⊓ Lτ').toScheme := ⟨⟨_, hmem τ z, hwτ'⟩⟩
  have hc : ∀ (σ : Aut Z) (U : (pullback Z.hom Z.hom).Opens),
      U ≤ Scheme.Hom.agreeLocus Z.hom (pullback.fst Z.hom Z.hom ≫ σ.asIso.hom.left)
        (pullback.snd Z.hom Z.hom) (h1 σ) →
      U.ι ≫ pullback.fst Z.hom Z.hom ≫ σ.asIso.hom.left = U.ι ≫ pullback.snd Z.hom Z.hom :=
    fun σ U hU => by
      rw [← Scheme.homOfLE_ι _ hU, Category.assoc, Category.assoc,
        Scheme.Hom.agreeLocus_ι_comp]
  have hc1 := hc τ (Lτ ⊓ Lτ') inf_le_left
  have hc2 := hc τ' (Lτ ⊓ Lτ') inf_le_right
  exact hne (aut_eq_of_comp_eq ((Lτ ⊓ Lτ').ι ≫ pullback.fst Z.hom Z.hom)
    ((Category.assoc _ _ _).trans (hc1.trans (hc2.symm.trans (Category.assoc _ _ _).symm))))

/-- **The cohomology of `Z ×_X Z`.** For a Galois cover `Z ⟶ X` and a proper `Z ⟶ Spec k`,
`h^n(Z ×_X Z, 𝒪) = #Aut(Z) · h^n(Z, 𝒪)`. -/
theorem finrank_cohomologyOverField_pullback_self (k : Type u) [Field k]
    (fZ : Z.left ⟶ Spec (.of k)) [IsProper fZ] (n : ℕ) :
    haveI : IsFinite Z.hom := Z.prop.1
    Module.finrank k (cohomologyOverField k (pullback.fst Z.hom Z.hom ≫ fZ)
        (SheafOfModules.unit (pullback Z.hom Z.hom).ringCatSheaf) n) =
      Nat.card (Aut Z) * Module.finrank k (cohomologyOverField k fZ
        (SheafOfModules.unit Z.left.ringCatSheaf) n) := by
  classical
  have : IsFinite Z.hom := Z.prop.1
  have : IsConnected Z := inferInstance
  let : Fintype (Aut Z) := Fintype.ofFinite _
  set fW := pullback.fst Z.hom Z.hom ≫ fZ
  let A : Aut Z → (pullback Z.hom Z.hom).Modules := fun τ =>
    (Scheme.Modules.pushforward (finiteEtaleAutGraph Z τ)).obj
      (SheafOfModules.unit Z.left.ringCatSheaf)
  have ecov : SheafOfModules.unit (pullback Z.hom Z.hom).ringCatSheaf ≅ ∏ᶜ A :=
    structureSheafDisjointCoverIso (fun _ => Z.left) (finiteEtaleAutGraph Z)
      (exists_finiteEtaleAutGraph_apply Z) (disjoint_range_finiteEtaleAutGraph Z)
  have hcomp : ∀ τ : Aut Z, finiteEtaleAutGraph Z τ ≫ fW = fZ := fun τ => by
    simp only [fW, finiteEtaleAutGraph_fst_assoc]
  have hpush (τ : Aut Z) : Module.finrank k (cohomologyOverField k fW (A τ) n) =
      Module.finrank k (cohomologyOverField k fZ (SheafOfModules.unit Z.left.ringCatSheaf) n) := by
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z.left
    refine (finrank_cohomologyOverField_pushforward_of_isAffineHom k (finiteEtaleAutGraph Z τ) fW
      (SheafOfModules.unit Z.left.ringCatSheaf) n).symm.trans ?_
    rw [hcomp]
  have hfin (τ : Aut Z) : FiniteDimensional k (cohomologyOverField k fW (A τ) n) := by
    have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k fZ
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z.left
    have : FiniteDimensional k (cohomologyOverField k fZ
        (SheafOfModules.unit Z.left.ringCatSheaf) n) :=
      finiteDimensional_cohomologyOverField_of_isProper k fZ _ n
    have e := cohomologyOverFieldPushforwardIsoOfIsAffineHom k (finiteEtaleAutGraph Z τ) fW
      (SheafOfModules.unit Z.left.ringCatSheaf) n
    rw [hcomp] at e
    exact Module.Finite.equiv e.toLinearEquiv
  calc Module.finrank k (cohomologyOverField k fW
        (SheafOfModules.unit (pullback Z.hom Z.hom).ringCatSheaf) n)
      = Module.finrank k (cohomologyOverField k fW (∏ᶜ A) n) :=
        (cohomologyOverFieldIso k fW ecov n).toLinearEquiv.finrank_eq
    _ = ∑ τ, Module.finrank k (cohomologyOverField k fW (A τ) n) :=
        finrank_cohomologyOverField_pi k fW A n hfin
    _ = ∑ _τ : Aut Z, Module.finrank k (cohomologyOverField k fZ
          (SheafOfModules.unit Z.left.ringCatSheaf) n) :=
        Finset.sum_congr rfl fun τ _ => hpush τ
    _ = Nat.card (Aut Z) * Module.finrank k (cohomologyOverField k fZ
          (SheafOfModules.unit Z.left.ringCatSheaf) n) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

/-- **The Riemann–Hurwitz formula for a Galois finite étale cover of a curve.** Let `X` be a
smooth, proper, geometrically irreducible curve over `k` and `Z ⟶ X` a Galois finite étale cover
with fibres of cardinality `d`, `Z` being again a smooth, proper, geometrically irreducible curve
over `k`. Then `g_Z - 1 = d (g_X - 1)`. -/
theorem genus_sub_one_eq_of_isGalois (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [GeometricallyIrreducible f] [Smooth f]
    [IsProper (Z.hom ≫ f)] [IsCurve k (Z.hom ≫ f)] [GeometricallyIrreducible (Z.hom ≫ f)]
    [Smooth (Z.hom ≫ f)] (base : GeometricPoint X) :
    (genus (Z.hom ≫ f) : ℤ) - 1 =
      Nat.card ((finiteEtaleFiberFunctor base).obj Z) * ((genus f : ℤ) - 1) := by
  classical
  have : IsFinite Z.hom := Z.prop.1
  have : Etale Z.hom := Z.prop.2
  have : IsConnected Z := inferInstance
  set d := Nat.card ((finiteEtaleFiberFunctor base).obj Z)
  set fZ := Z.hom ≫ f
  set E := (Scheme.Modules.pushforward Z.hom).obj (SheafOfModules.unit Z.left.ringCatSheaf)
  have hE : Stacks.Morphisms.IsFiniteLocallyFreeOfRank Z.hom d :=
    isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber base Z
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E d := hE.toIsFiniteLocallyFreeOfRank
  have hnc : ¬ ∃ y : X, ∀ x : Z.left, Z.hom.base x = y := by
    rintro ⟨y, hy⟩
    have : Nonempty Z.left := (connectedSpace_left_of_isConnected Z inferInstance).toNonempty
    have hsurj := surjective_of_finiteEtale Z
    have := nontrivial_of_isCurve f
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    exact hab ((hy a').trans (hy b').symm)
  have hdeg := (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank E d
    (genericPoint X)).symm.trans
    (fiberRank_pushforward_unit_genericPoint_eq_degreeOver k fZ f Z.hom rfl hnc)
  have h0 := curveDegree_pullback_eq_degreeOver_mul k fZ f Z.hom rfl hnc E d
  rw [← hdeg] at h0
  simp only [curveDegree] at h0
  have hdim : topologicalKrullDim Z.left ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := fZ)).le
  have hsq := IsPullback.of_hasPullback Z.hom Z.hom
  have hpb := Stacks.AlgebraicGeometry.AffineBaseChangeProjection.pullbackPushforwardUnitIso hsq
  obtain ⟨z⟩ := nonempty_fiber_of_isConnected (finiteEtaleFiberFintypeFunctor X base) Z
  have haut : Nat.card (Aut Z) = d := by
    exact Nat.card_congr (Equiv.ofBijective _
      (evaluation_aut_bijective_of_isGalois (finiteEtaleFiberFintypeFunctor X base) Z z))
  have h1 : ∀ n : ℕ, Module.finrank k (cohomologyOverField k fZ
      ((Scheme.Modules.pullback Z.hom).obj E) n) =
      d * Module.finrank k (cohomologyOverField k fZ
        (SheafOfModules.unit Z.left.ringCatSheaf) n) := by
    intro n
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
      (pullback Z.hom Z.hom)
    refine ((cohomologyOverFieldIso k fZ hpb n).toLinearEquiv.finrank_eq).trans ?_
    refine (finrank_cohomologyOverField_pushforward_of_isAffineHom k (pullback.fst Z.hom Z.hom) fZ
      (SheafOfModules.unit (pullback Z.hom Z.hom).ringCatSheaf) n).symm.trans ?_
    rw [finrank_cohomologyOverField_pullback_self Z k fZ n, haut]
  have h2 : ∀ n : ℕ, Module.finrank k (cohomologyOverField k f E n) =
      Module.finrank k (cohomologyOverField k fZ (SheafOfModules.unit Z.left.ringCatSheaf) n) := by
    intro n
    have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z.left
    exact (finrank_cohomologyOverField_pushforward_of_isAffineHom k Z.hom f _ n).symm
  simp only [h1, h2] at h0
  have hmul : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * ((d * Module.finrank k (cohomologyOverField k fZ
      (SheafOfModules.unit Z.left.ringCatSheaf) n) : ℕ) : ℤ)) =
      d * ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k fZ
        (SheafOfModules.unit Z.left.ringCatSheaf) n) : ℤ) := by
    rw [mul_finsum]
    exact finsum_congr fun n => by push_cast; ring
  simp only [Functor.id_obj] at h0
  rw [hmul, sub_self] at h0
  have hdpos : (0 : ℤ) < d := by
    have : Nonempty ((finiteEtaleFiberFunctor base).obj Z) := ⟨z⟩
    exact_mod_cast Nat.card_pos (α := (finiteEtaleFiberFunctor base).obj Z)
  have hχ : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k fZ
      (SheafOfModules.unit Z.left.ringCatSheaf) n) : ℤ)) =
      d * ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f
        (SheafOfModules.unit X.ringCatSheaf) n) : ℤ) := by
    have := h0.symm
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hdpos.ne'
    · linarith
  have hg : ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) [IsProper g] [Smooth g]
      [GeometricallyIrreducible g] (hY : topologicalKrullDim Y ≤ 1),
      1 - (genus g : ℤ) = ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k g
        (SheafOfModules.unit Y.ringCatSheaf) n) : ℤ) := by
    intro Y g _ _ _ hY
    have : GeometricallyIntegral g := Stacks.AbelMap.geometricallyIntegral_of_smooth g
    have hiso := isIso_globalSections_of_geometricallyIntegral k g
    let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    have h1 : Module.finrank k Γ(Y, ⊤) = 1 := by
      have hb : Function.Bijective (algebraMap k Γ(Y, ⊤)) :=
        (ConcreteCategory.isIso_iff_bijective _).1 hiso
      rw [← (LinearEquiv.ofBijective (Algebra.linearMap k Γ(Y, ⊤)) hb).finrank_eq,
        Module.finrank_self]
    exact one_sub_genus_eq_eulerCharacteristic_unit k g hY h1
  have hX := hg X f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  have hZ := hg Z.left fZ hdim
  rw [← hX, ← hZ] at hχ
  linarith

end AlgebraicGeometry

end
