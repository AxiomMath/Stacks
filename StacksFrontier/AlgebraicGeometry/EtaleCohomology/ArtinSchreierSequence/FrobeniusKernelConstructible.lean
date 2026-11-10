module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusModuleSurjectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CoefficientHypotheses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence

/-!
# The kernel of Frobenius minus the identity is constructible

Let `p` be a prime, let `S` be a scheme over `𝔽_p`, let `E` be a finite locally free module on
the small étale site of `S` and let `F` be a Frobenius-semilinear additive endomorphism of `E`.
Then the cokernel of `F - 1` is zero, by `AlgebraicGeometry.epi_frobeniusSemilinear_sub_id`, and
its kernel is a constructible abelian sheaf.

## Main results

* `AlgebraicGeometry.isConstructibleAbelianSheaf_of_etale_local`: an abelian sheaf whose inverse
  image along the members of an étale covering is constructible is constructible.
* `AlgebraicGeometry.frobeniusFixedScheme`: the affine étale `Y`-scheme of solutions of the
  Frobenius fixed-point equations `xᵢ = ∑ⱼ aⱼᵢ xⱼᵖ`, with its universal property
  `AlgebraicGeometry.frobeniusFixedScheme.exists_lift` and
  `AlgebraicGeometry.frobeniusFixedScheme.hom_ext`.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_kernel_frobeniusSemilinear_sub_id`: the kernel
  of `F - 1` is constructible.
* `AlgebraicGeometry.isZero_cokernel_and_isConstructible_kernel_frobeniusSemilinear_sub_id`: the
  cokernel of `F - 1` is zero and its kernel is constructible.

## Implementation notes

Over an affine object `V` of the small étale site over which `E` is
free on sections `s₁, …, sₙ`, with `F sⱼ = ∑ᵢ aⱼᵢ sᵢ`, a section `∑ⱼ xⱼ sⱼ` lies in the kernel of
`F - 1` exactly when `xᵢ = ∑ⱼ aⱼᵢ xⱼᵖ`. So the restriction of the kernel to `V` is represented by
the spectrum of `Γ(V)[x₁, …, xₙ]/(xᵢ - ∑ⱼ aⱼᵢ xⱼᵖ)`, which is étale over `V` by
`Algebra.frobeniusEquationAlgebra_isEtale`, and the represented sheaf is constructible by
Stacks 03S8 (`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs`). An abelian
sheaf is constructible when its underlying sheaf of sets is
(`AlgebraicGeometry.isConstructibleAbelianSheaf_of_underlying`), and constructibility descends
from such local pieces: Zariski locally by Stacks 095F and along a surjective morphism of
quasi-compact quasi-separated schemes by Stacks 095Q (2).

The module `E` and hence the kernel of `F - 1` have values in `AddCommGrpCat.{u}`, while the
constructibility predicates of this library are stated for the coefficient universe
`AddCommGrpCat.{u + 1}`, so the kernel is lifted along `AddCommGrpCat.uliftFunctor`, which does
not change its sections up to the canonical bijection.

## References

* [Stacks Project, Tag 0GKU](https://stacks.math.columbia.edu/tag/0GKU)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- Constructibility of an inverse image is transported along a commutative square: if
`b ≫ j = i ≫ g` and the inverse image of `G` along `g` is constructible, then so is the inverse
image along `b` of the inverse image of `G` along `j`. -/
private theorem isConstructibleAbelianSheaf_pullback_pullback_of_comp_eq {V W X T : B.Scheme}
    (b : V ⟶ W) (j : W ⟶ X) (i : V ⟶ T) (g : T ⟶ X) (hfac : b ≫ j = i ≫ g)
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hT : IsConstructibleAbelianSheaf B T ((smallEtaleAbelianPullbackFunctor B g).obj G)) :
    IsConstructibleAbelianSheaf B V
      ((smallEtaleAbelianPullbackFunctor B b).obj
        ((smallEtaleAbelianPullbackFunctor B j).obj G)) := by
  refine isConstructibleAbelianSheaf_congr B V
    ((smallEtaleSheafPullbackCompIso B V W X b j AddCommGrpCat.{u + 1}).app G).symm ?_
  rw [hfac]
  exact isConstructibleAbelianSheaf_congr B V
    ((smallEtaleSheafPullbackCompIso B V T X i g AddCommGrpCat.{u + 1}).app G)
    (isConstructibleFiniteSheaf_pullback B i _ hT)

/-- If the inverse image of an abelian sheaf `G` on `X` along an étale morphism `g : T ⟶ X` is
constructible, then every point in the image of `g` has an open neighbourhood `W` such that the
inverse image of `G` to `W` is constructible. -/
private theorem exists_opens_isConstructibleAbelianSheaf_pullback_of_etale (X : B.Scheme)
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) {T : B.Scheme}
    (g : T ⟶ X) [Etale (B.inclusion.map g)] {x : X.obj}
    (hx : x ∈ Set.range (B.inclusion.map g).base)
    (hT : IsConstructibleAbelianSheaf B T ((smallEtaleAbelianPullbackFunctor B g).obj G)) :
    ∃ (W : X.obj.Opens) (hW : B.Contains W), x ∈ W ∧
      IsConstructibleAbelianSheaf B (B.obj W hW)
        ((smallEtaleAbelianPullbackFunctor B
          (ObjectProperty.homMk W.ι : B.obj W hW ⟶ X)).obj G) := by
  let _ := fun (S T : B.Scheme) (g : T ⟶ S) =>
    SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat.{0, 0, u} B ℤ S T g
  let _ := fun (T : B.Scheme) (V : SmallEtale B T.obj T.property) =>
    SmallEtale.hasWeakSheafify_over_moduleCat.{0, 0, u} B ℤ T V
  obtain ⟨t, ht⟩ := hx
  let g₀ := B.inclusion.map g
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  obtain ⟨V, hV, htV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (U := g₀ ⁻¹ᵁ U) (x := t) (show g₀.base t ∈ U from ht ▸ hxU)
  let W : X.obj.Opens := ⟨g₀.base '' V, g₀.isOpenMap _ V.2⟩
  have hWU : (W : Set X.obj) ⊆ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact hVU hv
  have hWc : B.Contains W := Scheme.size_lt_of_isOpenImmersion W.ι X.property
  have hVc : B.Contains V := Scheme.size_lt_of_isOpenImmersion V.ι T.property
  let Wb := B.obj W hWc
  let Vb := B.obj V hVc
  let jW : Wb ⟶ X := ObjectProperty.homMk W.ι
  let iV : Vb ⟶ T := ObjectProperty.homMk V.ι
  have hrange : Set.range (V.ι ≫ g₀).base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨v, rfl⟩
    exact ⟨v.1, v.2, rfl⟩
  let h₀ : (V : Scheme) ⟶ W := IsOpenImmersion.lift W.ι (V.ι ≫ g₀) hrange
  let hb : Vb ⟶ Wb := ObjectProperty.homMk h₀
  have hfac : hb ≫ jW = iV ≫ g := by
    ext1
    exact IsOpenImmersion.lift_fac W.ι (V.ι ≫ g₀) hrange
  have hsurj : Function.Surjective (B.inclusion.map hb).base := by
    rintro ⟨_, v, hv, rfl⟩
    refine ⟨⟨v, hv⟩, ?_⟩
    apply W.ι.isOpenEmbedding.injective
    change (h₀ ≫ W.ι).base ⟨v, hv⟩ = _
    rw [IsOpenImmersion.lift_fac]
    rfl
  have : IsAffine (V : Scheme) := hV
  have hWcpt : CompactSpace Wb.obj := by
    change CompactSpace (W : Set X.obj)
    rw [← isCompact_iff_compactSpace]
    exact hV.isCompact.image g₀.continuous
  have hWqs : QuasiSeparatedSpace Wb.obj := by
    change QuasiSeparatedSpace (W : Set X.obj)
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _ W.2).1
      (hU.isQuasiSeparated.of_subset hWU)
  exact ⟨W, hWc, ⟨t, htV, ht⟩, (isConstructibleAbelianSheaf_pullback_iff_of_surjective B hb
    inferInstance inferInstance hWcpt hWqs hsurj _).2
      (isConstructibleAbelianSheaf_pullback_pullback_of_comp_eq B hb jW iV g hfac G hT)⟩

/-- **Constructibility is étale local.** An abelian sheaf on the small étale site of `X` is
constructible if every point of `X` is in the image of an étale morphism `T ⟶ X` along which the
inverse image of the sheaf is constructible. -/
theorem isConstructibleAbelianSheaf_of_etale_local (X : B.Scheme)
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (h : ∀ x : X.obj, ∃ (T : B.Scheme) (g : T ⟶ X), Etale (B.inclusion.map g) ∧
      x ∈ Set.range (B.inclusion.map g).base ∧
      IsConstructibleAbelianSheaf B T ((smallEtaleAbelianPullbackFunctor B g).obj G)) :
    IsConstructibleAbelianSheaf B X G := by
  classical
  have key (x : X.obj) : ∃ (W : X.obj.Opens) (hW : B.Contains W), x ∈ W ∧
      IsConstructibleAbelianSheaf B (B.obj W hW)
        ((smallEtaleAbelianPullbackFunctor B
          (ObjectProperty.homMk W.ι : B.obj W hW ⟶ X)).obj G) := by
    obtain ⟨T, g, _, hx, hT⟩ := h x
    exact exists_opens_isConstructibleAbelianSheaf_pullback_of_etale B X G g hx hT
  choose W hW hxW hWG using key
  refine isConstructibleFiniteSheaf_of_openCover B X G (fun x => B.obj (W x) (hW x))
    (fun x => (ObjectProperty.homMk (W x).ι : B.obj (W x) (hW x) ⟶ X))
    (fun x => (inferInstance : IsOpenImmersion (W x).ι)) ?_ hWG
  ext x
  simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
  exact ⟨x, by
    change x ∈ Set.range (W x).ι.base
    rw [Scheme.Opens.range_ι]
    exact hxW x⟩

/-- A sheaf of modules with a finite family of generating sections whose presenting morphism is
an isomorphism has linearly independent standard basis sections over every object. -/
private theorem generatingSections_sum_injective
    {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (σ : M.GeneratingSections)
    [Fintype σ.I] [IsIso σ.π] (U : Cᵒᵖ) :
    Function.Injective (fun c : σ.I → R.obj.obj U =>
      ∑ i, c i • (SheafOfModules.ιFree i ≫ σ.π).val.app U (1 : R.obj.obj U)) := by
  classical
  let G : σ.I → SheafOfModules.{u} R := fun _ => SheafOfModules.unit R
  let : HasBiproduct G := HasBiproduct.of_hasProduct G
  let e : SheafOfModules.free (R := R) σ.I ≅ biproduct G :=
    IsColimit.coconePointUniqueUpToIso
      (SheafOfModules.isColimitFreeCofan σ.I) (biproduct.isColimit G)
  have hi (i : σ.I) : SheafOfModules.ιFree i ≫ e.hom = biproduct.ι G i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (SheafOfModules.isColimitFreeCofan σ.I) (biproduct.isColimit G) (Discrete.mk i)
  let coord (k : σ.I) := ((inv σ.π ≫ e.hom ≫ biproduct.π G k).val.app U).hom
  have hcoord (k : σ.I) (c : σ.I → R.obj.obj U) :
      coord k (∑ i, c i • ((SheafOfModules.ιFree i ≫ σ.π).val.app U).hom
        (1 : R.obj.obj U)) = c k := by
    rw [map_sum]
    simp only [map_smul]
    have hδ (i : σ.I) : coord k (((SheafOfModules.ιFree i ≫ σ.π).val.app U).hom
        (1 : R.obj.obj U)) = (if i = k then (1 : R.obj.obj U) else 0 : R.obj.obj U) := by
      change ((SheafOfModules.ιFree i ≫ σ.π ≫ inv σ.π ≫ e.hom ≫ biproduct.π G k).val.app
        U).hom (1 : R.obj.obj U) = _
      rw [IsIso.hom_inv_id_assoc, reassoc_of% (hi i)]
      split_ifs with h
      · subst h
        rw [biproduct.ι_π_self]
        rfl
      · rw [biproduct.ι_π_ne _ h]
        rfl
    simp only [hδ]
    rw [Finset.sum_eq_single k (fun i _ hik => by
        simp only [hik, ite_false]
        change c i * 0 = 0
        rw [mul_zero])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp only [ite_true]
    change c k * 1 = c k
    rw [mul_one]
  intro c c' hcc'
  ext k
  rw [← hcoord k c, ← hcoord k c']
  exact congrArg (coord k) hcc'

/-- A sheaf of modules with a finite family of generating sections is spanned by the images of
the standard basis sections over every object. -/
private theorem generatingSections_sum_surjective
    {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (σ : M.GeneratingSections)
    [Fintype σ.I] [IsIso σ.π] (U : Cᵒᵖ) :
    Function.Surjective (fun c : σ.I → R.obj.obj U =>
      ∑ i, c i • (SheafOfModules.ιFree i ≫ σ.π).val.app U (1 : R.obj.obj U)) := by
  have hsmul (i : σ.I) (c : R.obj.obj U) :
      ((SheafOfModules.ιFree i ≫ σ.π).val.app U).hom c =
        c • ((SheafOfModules.ιFree i ≫ σ.π).val.app U).hom (1 : R.obj.obj U) := by
    rw [← ((SheafOfModules.ιFree i ≫ σ.π).val.app U).hom.map_smul c (1 : R.obj.obj U)]
    congr 1
    change c = c * 1
    rw [mul_one]
  intro x
  obtain ⟨a, ha⟩ := generatingSections_eq_sum σ U x
  refine ⟨a, ?_⟩
  rw [ha]
  exact Finset.sum_congr rfl fun i _ => (hsmul i (a i)).symm

/-- A sheaf of modules with a finite family of generating sections whose presenting morphism is
an isomorphism is free on the images of the standard basis sections over every object: every
section is a unique combination of them. -/
theorem generatingSections_sum_bijective
    {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (σ : M.GeneratingSections)
    [Fintype σ.I] [IsIso σ.π] (U : Cᵒᵖ) :
    Function.Bijective (fun c : σ.I → R.obj.obj U =>
      ∑ i, c i • (SheafOfModules.ιFree i ≫ σ.π).val.app U (1 : R.obj.obj U)) :=
  ⟨generatingSections_sum_injective σ U, generatingSections_sum_surjective σ U⟩

section FrobeniusFixedScheme

variable (p n : ℕ) (Y : Scheme.{u}) (a : Fin n → Fin n → Γ(Y, ⊤))

/-- The morphism of spectra induced by the algebra of the Frobenius fixed-point equations
`xᵢ = ∑ⱼ aⱼᵢ xⱼᵖ` over the global sections of `Y`. -/
noncomputable abbrev frobeniusFixedScheme.specMap :
    Spec (CommRingCat.of (frobeniusEquationAlgebra p n Γ(Y, ⊤) a 0)) ⟶ Spec Γ(Y, ⊤) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (frobeniusEquationAlgebra p n Γ(Y, ⊤) a 0)))

/-- The Spec of the algebra of the Frobenius fixed-point equations `xᵢ = ∑ⱼ aⱼᵢ xⱼᵖ` over the
global sections of `Y`, base changed to `Y`. Its points with values in a `Y`-scheme `T` are the
solutions of these equations in `Γ(T, ⊤)`. -/
noncomputable abbrev frobeniusFixedScheme : Scheme.{u} :=
  pullback (frobeniusFixedScheme.specMap p n Y a) Y.toSpecΓ

/-- The structure morphism of `AlgebraicGeometry.frobeniusFixedScheme`. -/
noncomputable def frobeniusFixedScheme.π : frobeniusFixedScheme p n Y a ⟶ Y :=
  pullback.snd (frobeniusFixedScheme.specMap p n Y a) Y.toSpecΓ

/-- The ring map from the algebra of the Frobenius equations to the global sections of
`AlgebraicGeometry.frobeniusFixedScheme`. -/
noncomputable def frobeniusFixedScheme.toΓ :
    frobeniusEquationAlgebra p n Γ(Y, ⊤) a 0 →+* Γ(frobeniusFixedScheme p n Y a, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (frobeniusEquationAlgebra p n Γ(Y, ⊤) a 0))).inv ≫
    (pullback.fst (frobeniusFixedScheme.specMap p n Y a) Y.toSpecΓ).appTop).hom

/-- The universal solution of the Frobenius equations on
`AlgebraicGeometry.frobeniusFixedScheme`. -/
noncomputable def frobeniusFixedScheme.coord (j : Fin n) : Γ(frobeniusFixedScheme p n Y a, ⊤) :=
  frobeniusFixedScheme.toΓ p n Y a (Ideal.Quotient.mk _ (MvPolynomial.X j))

/-- The constants of the algebra of the Frobenius equations go to the pullbacks of the global
sections of `Y`. -/
theorem frobeniusFixedScheme.toΓ_C (c : Γ(Y, ⊤)) :
    frobeniusFixedScheme.toΓ p n Y a (Ideal.Quotient.mk _ (MvPolynomial.C c)) =
      (frobeniusFixedScheme.π p n Y a).appTop c := by
  let A := Γ(Y, ⊤)
  let Q := frobeniusEquationAlgebra p n A a 0
  let g : Spec (.of Q) ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A Q))
  have hc : (CommRingCat.ofHom (algebraMap A Q)) ≫
      CommRingCat.ofHom (frobeniusFixedScheme.toΓ p n Y a) =
        (frobeniusFixedScheme.π p n Y a).appTop := by
    change CommRingCat.ofHom (algebraMap A Q) ≫ (Scheme.ΓSpecIso (.of Q)).inv ≫
      (pullback.fst g Y.toSpecΓ).appTop = (pullback.snd g Y.toSpecΓ).appTop
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop,
      Scheme.toSpecΓ_appTop]
    change (Scheme.ΓSpecIso A).inv ≫ (Scheme.ΓSpecIso A).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc]
  rw [show Ideal.Quotient.mk _ (MvPolynomial.C c) = algebraMap A Q c from rfl]
  exact ConcreteCategory.congr_hom hc c

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the algebra structures on `Γ(Y, ⊤)` and its quotient algebra
/-- The universal solution solves the Frobenius fixed-point equations. -/
theorem frobeniusFixedScheme.coord_eq (i : Fin n) :
    ∑ j, (frobeniusFixedScheme.π p n Y a).appTop (a j i) *
      frobeniusFixedScheme.coord p n Y a j ^ p = frobeniusFixedScheme.coord p n Y a i := by
  have hz : (Ideal.Quotient.mk _ (MvPolynomial.C ((0 : Fin n → Γ(Y, ⊤)) i) +
      MvPolynomial.X i - ∑ j, MvPolynomial.C (a j i) * MvPolynomial.X j ^ p) :
        frobeniusEquationAlgebra p n Γ(Y, ⊤) a 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hh := congrArg (frobeniusFixedScheme.toΓ p n Y a) hz
  simp only [map_sub, map_add, map_sum, map_mul, map_pow, frobeniusFixedScheme.toΓ_C] at hh
  simp only [Pi.zero_apply, map_zero] at hh
  change 0 + frobeniusFixedScheme.coord p n Y a i -
    ∑ j, _ * frobeniusFixedScheme.coord p n Y a j ^ p = 0 at hh
  linear_combination -hh

/-- The structure morphism of `AlgebraicGeometry.frobeniusFixedScheme` is étale when `p` is a
prime vanishing on `Y`. -/
theorem frobeniusFixedScheme.etale_π [Fact p.Prime]
    (hY : Stacks.Frobenius.IsInCharacteristic Y p) :
    Etale (frobeniusFixedScheme.π p n Y a) := by
  let A := Γ(Y, ⊤)
  let Q := frobeniusEquationAlgebra p n A a 0
  have : Algebra.Etale A Q := Algebra.frobeniusEquationAlgebra_isEtale p n A hY a 0
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap A Q))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (RingHom.etale_algebraMap.mpr inferInstance)
  change Etale (pullback.snd _ _)
  infer_instance

/-- A solution of the Frobenius equations on a `Y`-scheme `T` comes from a morphism of `Y`-schemes
to `AlgebraicGeometry.frobeniusFixedScheme`. -/
theorem frobeniusFixedScheme.exists_lift {T : Scheme.{u}} (t : T ⟶ Y) (c : Fin n → Γ(T, ⊤))
    (hc : ∀ i, ∑ j, t.appTop (a j i) * c j ^ p = c i) :
    ∃ f : T ⟶ frobeniusFixedScheme p n Y a, f ≫ frobeniusFixedScheme.π p n Y a = t ∧
      ∀ j, f.appTop (frobeniusFixedScheme.coord p n Y a j) = c j := by
  let A := Γ(Y, ⊤)
  let Q := frobeniusEquationAlgebra p n A a 0
  let g : Spec (.of Q) ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A Q))
  let ev : MvPolynomial (Fin n) A →+* Γ(T, ⊤) := MvPolynomial.eval₂Hom t.appTop.hom c
  have hker : Ideal.span (Set.range fun i : Fin n =>
      MvPolynomial.C ((0 : Fin n → A) i) + MvPolynomial.X i -
        ∑ j : Fin n, MvPolynomial.C (a j i) * MvPolynomial.X j ^ p) ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    simp only [ev, map_sub, map_sum, map_mul, map_pow, MvPolynomial.eval₂Hom_C,
      MvPolynomial.eval₂Hom_X', Pi.zero_apply, map_zero, zero_add]
    rw [hc i, sub_self]
  let ψ : Q →+* Γ(T, ⊤) := Ideal.Quotient.lift _ ev (fun z hz => RingHom.mem_ker.mp (hker hz))
  have hψC (z : A) : ψ (algebraMap A Q z) = t.appTop z := by
    change ev (MvPolynomial.C z) = _
    simp only [ev, MvPolynomial.eval₂Hom_C]
  let φ : T ⟶ Spec (.of Q) := T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have hφ : φ ≫ g = t ≫ Y.toSpecΓ := by
    rw [Scheme.toSpecΓ_naturality]
    simp only [φ, g, Category.assoc, ← Spec.map_comp]
    congr 2
    ext z
    exact hψC z
  refine ⟨pullback.lift φ t hφ, pullback.lift_snd _ _ _, fun j => ?_⟩
  change ((Scheme.ΓSpecIso (.of Q)).inv ≫ (pullback.fst g Y.toSpecΓ).appTop ≫
    (pullback.lift φ t hφ).appTop) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = c j
  rw [← Scheme.Hom.comp_appTop, pullback.lift_fst]
  simp only [φ, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  change ev (MvPolynomial.X j) = c j
  simp only [ev, MvPolynomial.eval₂Hom_X']

/-- A morphism of `Y`-schemes to `AlgebraicGeometry.frobeniusFixedScheme` is determined by the
solution of the Frobenius equations it pulls back. -/
theorem frobeniusFixedScheme.hom_ext {T : Scheme.{u}} (f f' : T ⟶ frobeniusFixedScheme p n Y a)
    (h : f ≫ frobeniusFixedScheme.π p n Y a = f' ≫ frobeniusFixedScheme.π p n Y a)
    (hc : ∀ j, f.appTop (frobeniusFixedScheme.coord p n Y a j) =
      f'.appTop (frobeniusFixedScheme.coord p n Y a j)) : f = f' := by
  let g := frobeniusFixedScheme.specMap p n Y a
  apply pullback.hom_ext _ h
  apply ext_of_isAffine
  rw [← cancel_epi
    (Scheme.ΓSpecIso (CommRingCat.of (frobeniusEquationAlgebra p n Γ(Y, ⊤) a 0))).inv]
  ext1
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    have hz := congrArg (fun k => k.appTop z) h
    simp only [Scheme.Hom.comp_appTop] at hz
    have h2 : ∀ k : T ⟶ frobeniusFixedScheme p n Y a,
        ((Scheme.ΓSpecIso (CommRingCat.of (frobeniusEquationAlgebra p n Γ(Y, ⊤) a 0))).inv ≫
          (k ≫ pullback.fst g Y.toSpecΓ).appTop).hom
          ((Ideal.Quotient.mk _).comp MvPolynomial.C z) =
        k.appTop ((frobeniusFixedScheme.π p n Y a).appTop z) := by
      intro k
      change k.appTop (frobeniusFixedScheme.toΓ p n Y a
        (Ideal.Quotient.mk _ (MvPolynomial.C z))) = _
      rw [frobeniusFixedScheme.toΓ_C]
    exact (h2 f).trans (hz.trans (h2 f').symm)
  · exact hc

/-- Over an affine scheme, `AlgebraicGeometry.frobeniusFixedScheme` is affine. -/
theorem frobeniusFixedScheme.isAffine [IsAffine Y] :
    IsAffine (frobeniusFixedScheme p n Y a) := by
  have : IsAffineHom (frobeniusFixedScheme.π p n Y a) := by
    change IsAffineHom (pullback.snd _ _)
    infer_instance
  exact isAffine_of_isAffineHom (frobeniusFixedScheme.π p n Y a)

end FrobeniusFixedScheme

/-- `AlgebraicGeometry.frobeniusFixedScheme` as an object of the small étale site of `Y`, when `p`
is a prime vanishing on `Y`. -/
private noncomputable def frobeniusFixedEtale (p n : ℕ) [Fact p.Prime]
    (Y : B.Scheme) [IsAffine Y.obj] (a : Fin n → Fin n → Γ(Y.obj, ⊤))
    (hY : Stacks.Frobenius.IsInCharacteristic Y.obj p) :
    SmallEtale B Y.obj Y.property :=
  have := frobeniusFixedScheme.etale_π p n Y.obj a hY
  have := frobeniusFixedScheme.isAffine p n Y.obj a
  ⟨Over.mk (ObjectProperty.homMk (frobeniusFixedScheme.π p n Y.obj a) :
    B.obj (frobeniusFixedScheme p n Y.obj a)
      (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
        (frobeniusFixedScheme.π p n Y.obj a) Y.property) ⟶ B.obj Y.obj Y.property),
    frobeniusFixedScheme.etale_π p n Y.obj a hY⟩

/-- A morphism to `AlgebraicGeometry.frobeniusFixedEtale` is determined by the solution of the
Frobenius equations it pulls back. -/
private theorem frobeniusFixedEtale.hom_ext (p n : ℕ) [Fact p.Prime]
    (Y : B.Scheme) [IsAffine Y.obj] (a : Fin n → Fin n → Γ(Y.obj, ⊤))
    (hY : Stacks.Frobenius.IsInCharacteristic Y.obj p)
    {T : SmallEtale B Y.obj Y.property}
    (f₁ f₂ : T ⟶ frobeniusFixedEtale B p n Y a hY)
    (h : ∀ j, (B.inclusion.map f₁.hom.left).appTop (frobeniusFixedScheme.coord p n Y.obj a j) =
      (B.inclusion.map f₂.hom.left).appTop (frobeniusFixedScheme.coord p n Y.obj a j)) :
    f₁ = f₂ := by
  have hw (f : T ⟶ frobeniusFixedEtale B p n Y a hY) :
      B.inclusion.map f.hom.left ≫ frobeniusFixedScheme.π p n Y.obj a =
        B.inclusion.map T.obj.hom :=
    congrArg (fun k => B.inclusion.map k) (Over.w f.hom)
  exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (frobeniusFixedScheme.hom_ext p n Y.obj a _ _ ((hw f₁).trans (hw f₂).symm) h)))

/-- A solution of the Frobenius equations over an object `T` of the small étale site of `Y` comes
from a morphism `T ⟶ AlgebraicGeometry.frobeniusFixedEtale`. -/
private theorem frobeniusFixedEtale.exists_lift (p n : ℕ) [Fact p.Prime]
    (Y : B.Scheme) [IsAffine Y.obj] (a : Fin n → Fin n → Γ(Y.obj, ⊤))
    (hY : Stacks.Frobenius.IsInCharacteristic Y.obj p)
    (T : SmallEtale B Y.obj Y.property)
    (c : Fin n → Γ(B.inclusion.obj T.obj.left, ⊤))
    (hc : ∀ i, ∑ j, (B.inclusion.map T.obj.hom).appTop (a j i) * c j ^ p = c i) :
    ∃ f : T ⟶ frobeniusFixedEtale B p n Y a hY,
      ∀ j, (B.inclusion.map f.hom.left).appTop (frobeniusFixedScheme.coord p n Y.obj a j) =
        c j := by
  obtain ⟨f₀, hf₀, hf₀c⟩ := frobeniusFixedScheme.exists_lift p n Y.obj a _ c hc
  exact ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk f₀) (by
    ext1
    exact hf₀)), hf₀c⟩

/-- Restriction of a sheaf of modules commutes with finite linear combinations. -/
private theorem _root_.SheafOfModules.val_map_sum_smul {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} (E : SheafOfModules.{u} R)
    {T₁ T₂ : C} (g : T₁ ⟶ T₂) {ι : Type*} [Fintype ι] (c : ι → R.obj.obj (op T₂))
    (t : ι → E.val.obj (op T₂)) :
    E.val.map g.op (∑ j, c j • t j) = ∑ j, R.obj.map g.op (c j) • E.val.map g.op (t j) := by
  rw [map_sum]
  simp only [E.val.map_smul]

/-- If `G` is `p`-semilinear with `G sⱼ = ∑ᵢ aⱼᵢ sᵢ` and `cᵢ = ∑ⱼ aⱼᵢ cⱼᵖ`, then `∑ⱼ cⱼ sⱼ` is
fixed by `G`. -/
private theorem frobenius_sub_id_sum_eq_zero {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (p n : ℕ) (G : M →+ M)
    (hG : ∀ (a : A) (x : M), G (a • x) = a ^ p • G x) (s : Fin n → M) (a : Fin n → Fin n → A)
    (ha : ∀ j, G (s j) = ∑ i, a j i • s i) (c : Fin n → A)
    (hc : ∀ i, ∑ j, a j i * c j ^ p = c i) :
    G (∑ j, c j • s j) - ∑ j, c j • s j = 0 := by
  simpa only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] using
    frobenius_sub_id_sum p n G hG s a 0 c ha fun i => by rw [hc, sub_self]; rfl

/-- If `G` is `p`-semilinear with `G sⱼ = ∑ᵢ aⱼᵢ sᵢ`, the `sⱼ` are linearly independent and
`∑ⱼ cⱼ sⱼ` is fixed by `G`, then `cᵢ = ∑ⱼ aⱼᵢ cⱼᵖ`. -/
private theorem frobenius_coeff_eq_of_sub_id_sum_eq_zero {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (p n : ℕ) (G : M →+ M)
    (hG : ∀ (a : A) (x : M), G (a • x) = a ^ p • G x) (s : Fin n → M) (a : Fin n → Fin n → A)
    (ha : ∀ j, G (s j) = ∑ i, a j i • s i) (c : Fin n → A)
    (hs : Function.Injective fun c : Fin n → A => ∑ j, c j • s j)
    (hc : G (∑ j, c j • s j) - ∑ j, c j • s j = 0) (i : Fin n) :
    ∑ j, a j i * c j ^ p = c i := by
  have key := frobenius_sub_id_sum p n G hG s a (fun i => (∑ j, a j i * c j ^ p) - c i) c ha
    fun _ => rfl
  have h0 : ∑ i, ((∑ j, a j i * c j ^ p) - c i) • s i = ∑ i, (0 : Fin n → A) i • s i := by
    rw [← key, hc]
    simp
  exact sub_eq_zero.mp (congrFun (hs h0) i)

/-- The sections of the kernel of a morphism of abelian sheaves over an object are the kernel of
the morphism on sections there: the inclusion is injective and its image is the kernel. -/
private theorem kernel_ι_app_injective_and_exists {C : Type*} [Category C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u}]
    {M N : Sheaf J AddCommGrpCat.{u}} (φ : M ⟶ N) (U : Cᵒᵖ) :
    Function.Injective ((kernel.ι φ).hom.app U) ∧
      ∀ e : M.obj.obj U, φ.hom.app U e = 0 → ∃ k, (kernel.ι φ).hom.app U k = e := by
  let G : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation _ _).obj U
  let e := PreservesKernel.iso G φ ≪≫ AddCommGrpCat.kernelIsoKer (G.map φ)
  have he : (kernel.ι φ).hom.app U = e.hom ≫
      AddCommGrpCat.ofHom (AddSubgroup.subtype (G.map φ).hom.ker) := by
    simp only [e, Iso.trans_hom, Category.assoc, AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rfl
  refine ⟨?_, fun x hx => ?_⟩
  · rw [he]
    exact fun a b hab =>
      (ConcreteCategory.injective_of_mono_of_preservesPullback e.hom) (Subtype.ext hab)
  · refine ⟨e.inv ⟨x, hx⟩, ?_⟩
    rw [he]
    change ((e.inv ≫ e.hom) _).1 = x
    simp

section Local

open Stacks.Frobenius

variable (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) (hS : B.Contains S)
  (E : SheafOfModules.{u} (SmallEtale.structureSheaf B S hS))
  (F : ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E) ⟶
    ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E))
  (hF : ∀ (U : SmallEtale B S hS)
    (a : (SmallEtale.structureSheaf B S hS).obj.obj (op U))
    (e : E.val.obj (op U)),
    SheafOfModules.sectionsAddHom F (op U) (a • e) =
      a ^ p • SheafOfModules.sectionsAddHom F (op U) e)

/-- Over an object `V` of the small étale site on which `E` is spanned by the sections `s`, the
endomorphism `F` has a matrix `a` with `F sⱼ = ∑ᵢ aⱼᵢ sᵢ`, compatibly with restriction. -/
private theorem exists_sectionsAddHom_map_eq_sum (V : SmallEtale B S hS) (n : ℕ)
    (s : Fin n → E.val.obj (op V))
    (hs : Function.Surjective (fun c : Fin n → (SmallEtale.structureSheaf B S hS).obj.obj (op V) =>
      ∑ j, c j • E.val.map (𝟙 V).op (s j))) :
    ∃ a : Fin n → Fin n → (SmallEtale.structureSheaf B S hS).obj.obj (op V),
      ∀ (T : SmallEtale B S hS) (f : T ⟶ V) (j : Fin n),
        SheafOfModules.sectionsAddHom F (op T) (E.val.map f.op (s j)) =
          ∑ i, (SmallEtale.structureSheaf B S hS).obj.map f.op (a j i) • E.val.map f.op (s i) := by
  have hmapid : ∀ e : E.val.obj (op V), E.val.map (𝟙 V).op e = e := fun e => by
    rw [op_id, E.val.map_id]
    rfl
  choose a ha using fun j => hs (SheafOfModules.sectionsAddHom F (op V) (s j))
  simp only [hmapid] at ha
  refine ⟨a, fun T f j => ?_⟩
  have hnat : SheafOfModules.sectionsAddHom F (op T) (E.val.map f.op (s j)) =
      E.val.map f.op (SheafOfModules.sectionsAddHom F (op V) (s j)) :=
    ConcreteCategory.congr_hom (F.hom.naturality f.op) (s j)
  rw [hnat, ← ha j]
  exact SheafOfModules.val_map_sum_smul E f (a j) s

/-- An abelian sheaf `K` on the small étale site of `S` whose restriction to `V`, as a sheaf of
sets, is represented by an object `W` of the small étale site of `V` has constructible inverse
image to `V`, when the underlying schemes of `V` and `W` are quasi-compact and
quasi-separated. -/
private theorem isConstructibleAbelianSheaf_pullback_of_bijective (V : SmallEtale B S hS)
    [CompactSpace V.obj.left.obj] [QuasiSeparatedSpace V.obj.left.obj]
    (K : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})
    (W : SmallEtale B V.obj.left.obj V.obj.left.property)
    [CompactSpace W.obj.left.obj] [QuasiSeparatedSpace W.obj.left.obj]
    (ξ : K.obj.obj (op ((smallEtalePostcompose B S hS V).obj W)))
    (h : ∀ T, Function.Bijective fun f : T ⟶ W =>
      K.obj.map ((smallEtalePostcompose B S hS V).map f).op ξ) :
    IsConstructibleAbelianSheaf B V.obj.left
      ((smallEtaleAbelianPullbackFunctor B V.obj.hom).obj
        ((sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          K)) := by
  let Y := V.obj.left
  let JY := SmallEtale.topology B Y.obj Y.property
  let K' := (sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj K
  let P := (smallEtaleUnderlyingSetSheaf B Y).obj
    (((smallEtalePostcompose B S hS V).sheafPushforwardContinuous AddCommGrpCat.{u + 1} JY
      (SmallEtale.topology B S hS)).obj K')
  let ξ' : P.obj.obj (op W) := ULift.up ξ
  let α := uliftYonedaEquiv.{u + 1}.symm ξ'
  have hbij (T : SmallEtale B Y.obj Y.property) : Function.Bijective (α.app (op T)) := by
    refine ⟨?_, fun ⟨k⟩ => ?_⟩
    · rintro ⟨f₁⟩ ⟨f₂⟩ hf
      have : K.obj.map ((smallEtalePostcompose B S hS V).map f₁).op ξ =
          K.obj.map ((smallEtalePostcompose B S hS V).map f₂).op ξ :=
        congrArg ULift.down hf
      exact congrArg ULift.up ((h T).1 this)
    · obtain ⟨f, hf⟩ := (h T).2 k
      exact ⟨ULift.up f, congrArg ULift.up hf⟩
  have : ∀ T, IsIso (α.app T) := fun T => (isIso_iff_bijective _).2 (hbij T.unop)
  have : IsIso α := NatIso.isIso_of_isIso_app _
  refine isConstructibleAbelianSheaf_congr B Y
    ((smallEtaleSheafPullbackIsoPostcompose B S hS V AddCommGrpCat.{u + 1}).app K').symm ?_
  refine isConstructibleAbelianSheaf_of_underlying B Y (smallEtaleUnderlyingSetCommutes B Y) ?_
  exact isConstructibleFiniteSheaf_congr B Y
    ((presheafToSheaf JY _).mapIso (asIso α) ≪≫ (sheafificationIso P).symm)
    (isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B Y W)

/-- Let `σ` be generating sections of `E` over `X` whose presenting morphism is an isomorphism and
let `h₀ : V ⟶ X`. Over every `T ⟶ V`, the module `E` is free on the restrictions of the standard
basis sections of `σ` over `V`, indexed through `eI`. -/
private theorem bijective_sum_smul_map_generatingSections {X V : SmallEtale B S hS}
    (σ : (E.over X).GeneratingSections) [Finite σ.I] [IsIso σ.π] (h₀ : V ⟶ X) {n : ℕ}
    (eI : Fin n ≃ σ.I) (T : SmallEtale B S hS) (f : T ⟶ V) :
    Function.Bijective (fun c : Fin n → (SmallEtale.structureSheaf B S hS).obj.obj (op T) =>
      ∑ j, c j • E.val.map f.op ((SheafOfModules.ιFree (eI j) ≫ σ.π).val.app
        (op (Over.mk h₀)) (1 : (SmallEtale.structureSheaf B S hS).obj.obj (op V)))) := by
  let := Fintype.ofFinite σ.I
  let b (Y : Over X) (k : σ.I) : E.val.obj (op Y.left) :=
    (SheafOfModules.ιFree k ≫ σ.π).val.app (op Y) (1 : (SmallEtale.structureSheaf B S hS).obj.obj
      (op Y.left))
  have hnat : ∀ {Y₁ Y₂ : Over X} (h : Y₁ ⟶ Y₂) (k : σ.I),
      E.val.map h.left.op (b Y₂ k) = b Y₁ k := by
    intro Y₁ Y₂ h k
    refine (PresheafOfModules.naturality_apply (SheafOfModules.ιFree k ≫ σ.π).val h.op
      (1 : (SmallEtale.structureSheaf B S hS).obj.obj (op Y₂.left))).symm.trans ?_
    congr 1
    exact (RingCat.Hom.hom ((SmallEtale.structureSheaf B S hS).obj.map h.left.op)).map_one
  have hs : ∀ j, E.val.map f.op (b (Over.mk h₀) (eI j)) = b (Over.mk (f ≫ h₀)) (eI j) :=
    fun j => hnat (Over.homMk f : Over.mk (f ≫ h₀) ⟶ Over.mk h₀) (eI j)
  have hfun : (fun c : Fin n → (SmallEtale.structureSheaf B S hS).obj.obj (op T) =>
      ∑ j, c j • E.val.map f.op (b (Over.mk h₀) (eI j))) =
        (fun d : σ.I → (SmallEtale.structureSheaf B S hS).obj.obj (op T) =>
          ∑ k, d k • b (Over.mk (f ≫ h₀)) k) ∘ (eI.arrowCongr (Equiv.refl _)) := by
    funext c
    simp only [Function.comp_apply, hs]
    rw [← Equiv.sum_comp eI]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Equiv.arrowCongr_apply, Function.comp_apply, Function.comp_apply,
      Equiv.symm_apply_apply]
    rfl
  change Function.Bijective (fun c : Fin n → (SmallEtale.structureSheaf B S hS).obj.obj (op T) =>
    ∑ j, c j • E.val.map f.op (b (Over.mk h₀) (eI j)))
  rw [hfun]
  exact (generatingSections_sum_bijective σ (op (Over.mk (f ≫ h₀)))).comp
    (eI.arrowCongr (Equiv.refl _)).bijective

include hF in
/-- Let `V` be an affine object of the small étale site of `S` in characteristic `p` and let `a`
be the matrix of `F` on sections `s` of `E` over `V`. The universal solution of the Frobenius
equations gives a section of the kernel of `F - 1` over
`AlgebraicGeometry.frobeniusFixedEtale`, whose restriction along `f : T ⟶ frobeniusFixedEtale` is
the combination of the restrictions of `s` with the coordinates of `f`. -/
private theorem exists_kernel_section_frobeniusFixedEtale (V : SmallEtale B S hS)
    [IsAffine V.obj.left.obj] (hc : IsInCharacteristic V.obj.left.obj p) (n : ℕ)
    (s : Fin n → E.val.obj (op V)) (a : Fin n → Fin n → Γ(V.obj.left.obj, ⊤))
    (ha : ∀ (T : SmallEtale B S hS) (f : T ⟶ V) (j : Fin n),
      SheafOfModules.sectionsAddHom F (op T) (E.val.map f.op (s j)) =
        ∑ i, (SmallEtale.structureSheaf B S hS).obj.map f.op (a j i) • E.val.map f.op (s i)) :
    ∃ ξ₀ : (kernel (F - 𝟙 _)).obj.obj
        (op ((smallEtalePostcompose B S hS V).obj (frobeniusFixedEtale B p n V.obj.left a hc))),
      ∀ (T : SmallEtale B V.obj.left.obj V.obj.left.property)
        (f : T ⟶ frobeniusFixedEtale B p n V.obj.left a hc),
        (kernel.ι
            (F - 𝟙 ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E))).hom.app
          (op ((smallEtalePostcompose B S hS V).obj T))
          ((kernel (F - 𝟙 _)).obj.map ((smallEtalePostcompose B S hS V).map f).op ξ₀) =
        ∑ j, (SmallEtale.structureSheaf B S hS).obj.map ((smallEtalePostcompose B S hS V).map f).op
          (frobeniusFixedScheme.coord p n V.obj.left.obj a j) •
            E.val.map (ObjectProperty.homMk (Over.homMk T.obj.hom) :
              (smallEtalePostcompose B S hS V).obj T ⟶ V).op (s j) := by
  let R := SmallEtale.structureSheaf B S hS
  let Y := V.obj.left
  let ι := kernel.ι (F - 𝟙 _)
  let Wobj := frobeniusFixedEtale B p n Y a hc
  let pc := smallEtalePostcompose B S hS V
  let toV (T : SmallEtale B Y.obj Y.property) : pc.obj T ⟶ V :=
    ObjectProperty.homMk (Over.homMk T.obj.hom)
  let s' (T : SmallEtale B Y.obj Y.property) (j : Fin n) : E.val.obj (op (pc.obj T)) :=
    E.val.map (toV T).op (s j)
  let xb : Fin n → R.obj.obj (op (pc.obj Wobj)) := frobeniusFixedScheme.coord p n Y.obj a
  have hξ : (F - 𝟙 _).hom.app (op (pc.obj Wobj)) (∑ j, xb j • s' Wobj j) = 0 := by
    let AW := Γ(frobeniusFixedScheme p n Y.obj a, ⊤)
    let : Module AW (E.val.obj (op (pc.obj Wobj))) := (E.val.obj (op (pc.obj Wobj))).isModule
    exact frobenius_sub_id_sum_eq_zero (A := AW) (M := E.val.obj (op (pc.obj Wobj))) p n
      (SheafOfModules.sectionsAddHom F _) (hF (pc.obj Wobj)) (s' Wobj)
      (fun j i => (frobeniusFixedScheme.π p n Y.obj a).appTop (a j i)) (ha _ (toV Wobj))
      (frobeniusFixedScheme.coord p n Y.obj a) (frobeniusFixedScheme.coord_eq p n Y.obj a)
  obtain ⟨ξ₀, hξ₀⟩ := (kernel_ι_app_injective_and_exists (F - 𝟙 _) (op (pc.obj Wobj))).2 _ hξ
  refine ⟨ξ₀, fun T f => ?_⟩
  have hcomp : pc.map f ≫ toV Wobj = toV T := by
    ext
    exact congrArg (fun k => B.inclusion.map k) (Over.w f.hom)
  refine (ConcreteCategory.congr_hom (ι.hom.naturality (pc.map f).op) ξ₀).trans ?_
  change E.val.map (pc.map f).op (ι.hom.app _ ξ₀) = _
  rw [hξ₀]
  refine (SheafOfModules.val_map_sum_smul E (pc.map f) xb (s' Wobj)).trans
    (Finset.sum_congr rfl fun j _ => ?_)
  congr 1
  change E.val.map (pc.map f).op (E.val.map (toV Wobj).op (s j)) = E.val.map (toV T).op (s j)
  rw [← hcomp, op_comp, E.val.map_comp]
  rfl

include hF in
/-- **The kernel of `F - 1` is constructible over a trivializing affine object.** Let `V` be an
object of the small étale site of `S` with affine underlying scheme in characteristic `p`, over
which `E` is free on the sections `s`. Then the inverse image to `V` of the kernel of `F - 1` is
a constructible abelian sheaf. -/
theorem isConstructibleAbelianSheaf_pullback_kernel_frobenius_sub_one
    (V : SmallEtale B S hS) [IsAffine V.obj.left.obj]
    (hc : IsInCharacteristic V.obj.left.obj p) (n : ℕ) (s : Fin n → E.val.obj (op V))
    (hbasis : ∀ (T : SmallEtale B S hS) (f : T ⟶ V),
      Function.Bijective (fun c : Fin n → (SmallEtale.structureSheaf B S hS).obj.obj (op T) =>
        ∑ j, c j • E.val.map f.op (s j))) :
    IsConstructibleAbelianSheaf B V.obj.left
      ((smallEtaleAbelianPullbackFunctor B V.obj.hom).obj
        ((sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (kernel (F - 𝟙 _)))) := by
  classical
  let R := SmallEtale.structureSheaf B S hS
  let Y := V.obj.left
  let ι := kernel.ι (F - 𝟙 _)
  have hι := kernel_ι_app_injective_and_exists (F - 𝟙 _)
  obtain ⟨a, ha⟩ := exists_sectionsAddHom_map_eq_sum B S hS E F V n s (hbasis V (𝟙 V)).2
  let a' : Fin n → Fin n → Γ(Y.obj, ⊤) := a
  let Wobj := frobeniusFixedEtale B p n Y a' hc
  let pc := smallEtalePostcompose B S hS V
  let toV (T : SmallEtale B Y.obj Y.property) : pc.obj T ⟶ V :=
    ObjectProperty.homMk (Over.homMk T.obj.hom)
  let s' (T : SmallEtale B Y.obj Y.property) (j : Fin n) : E.val.obj (op (pc.obj T)) :=
    E.val.map (toV T).op (s j)
  obtain ⟨ξ₀, hform⟩ :=
    exists_kernel_section_frobeniusFixedEtale B p S hS E F hF V hc n s a' ha
  have := frobeniusFixedScheme.isAffine p n Y.obj a'
  have : CompactSpace Wobj.obj.left.obj :=
    (inferInstance : CompactSpace (frobeniusFixedScheme p n Y.obj a'))
  have : QuasiSeparatedSpace Wobj.obj.left.obj :=
    (inferInstance : QuasiSeparatedSpace (frobeniusFixedScheme p n Y.obj a'))
  refine isConstructibleAbelianSheaf_pullback_of_bijective B S hS V _ Wobj ξ₀ fun T =>
    ⟨fun f₁ f₂ h => ?_, fun k => ?_⟩
  · have h' := congrArg (ι.hom.app (op (pc.obj T))) h
    dsimp only at h'
    rw [hform, hform] at h'
    exact frobeniusFixedEtale.hom_ext B p n Y a' hc f₁ f₂
      (congrFun ((hbasis (pc.obj T) (toV T)).1 h'))
  · obtain ⟨c, hcx⟩ := (hbasis (pc.obj T) (toV T)).2 (ι.hom.app (op (pc.obj T)) k)
    have hk : (F - 𝟙 _).hom.app (op (pc.obj T)) (ι.hom.app (op (pc.obj T)) k) = 0 :=
      congrArg (fun φ : kernel (F - 𝟙 _) ⟶ (SheafOfModules.toSheaf R).obj E =>
        φ.hom.app (op (pc.obj T)) k) (kernel.condition (F - 𝟙 _))
    let AT := Γ(B.inclusion.obj T.obj.left, ⊤)
    let : Module AT (E.val.obj (op (pc.obj T))) := (E.val.obj (op (pc.obj T))).isModule
    obtain ⟨f, hf⟩ := frobeniusFixedEtale.exists_lift B p n Y a' hc T c
      (frobenius_coeff_eq_of_sub_id_sum_eq_zero (A := AT) (M := E.val.obj (op (pc.obj T))) p n
        (SheafOfModules.sectionsAddHom F _) (hF (pc.obj T)) (s' T)
        (fun j i => (B.inclusion.map T.obj.hom).appTop (a' j i)) (ha _ (toV T)) c
        (hbasis (pc.obj T) (toV T)).1
        ((congrArg ((F - 𝟙 _).hom.app (op (pc.obj T))) hcx).trans hk))
    refine ⟨f, (hι (op (pc.obj T))).1 ((hform T f).trans ?_)⟩
    exact (Finset.sum_congr rfl fun j _ => congrArg (fun z => z • s' T j) (hf j)).trans hcx

end Local

open Stacks.Frobenius in
/-- **The kernel of `F - 1` is constructible.** Let `S` be a scheme in characteristic `p`, let `E`
be a finite locally free module on the small étale site of `S` and let `F` be a
Frobenius-semilinear additive endomorphism of `E`. Then the kernel of `F - 1` is a constructible
abelian sheaf. -/
theorem isConstructibleAbelianSheaf_kernel_frobeniusSemilinear_sub_id
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) (hS : B.Contains S)
    (E : SheafOfModules.{u} (SmallEtale.structureSheaf B S hS))
    [SheafOfModules.IsFiniteLocallyFree E]
    (hchar : IsInCharacteristic S p)
    (F : ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E) ⟶
      ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E))
    (hF : ∀ (U : SmallEtale B S hS)
      (a : (SmallEtale.structureSheaf B S hS).obj.obj (op U))
      (e : E.val.obj (op U)),
      SheafOfModules.sectionsAddHom F (op U) (a • e) =
        a ^ p • SheafOfModules.sectionsAddHom F (op U) e) :
    IsConstructibleAbelianSheaf B (B.obj S hS)
      ((sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (kernel (F - 𝟙 _))) := by
  classical
  obtain ⟨q, hq, hfin⟩ :=
    SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData (M := E)
  refine isConstructibleAbelianSheaf_of_etale_local B (B.obj S hS) _ fun x => ?_
  obtain ⟨W, g, ⟨i, ⟨g'⟩⟩, ⟨w, hw⟩⟩ := SmallEtale.exists_mem_arrows_mem_range B S hS
    (q.coversTop (SmallEtale.final B S hS)) (show S from x)
  obtain ⟨V₀, hV₀, hwV₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : W.obj.left.obj.Opens)) (x := w) trivial
  have hV₀c : B.Contains V₀ := Scheme.size_lt_of_isOpenImmersion V₀.ι W.obj.left.property
  let V : SmallEtale B S hS := ⟨Over.mk (ObjectProperty.homMk V₀.ι ≫ W.obj.hom :
    B.obj V₀ hV₀c ⟶ B.obj S hS), by
      change Etale (V₀.ι ≫ B.inclusion.map W.obj.hom)
      infer_instance⟩
  let jV : V ⟶ W := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk V₀.ι) rfl)
  have : IsAffine V.obj.left.obj := hV₀
  let σ := q.generators i
  let := hfin.isFiniteType i
  let : Fintype σ.I := Fintype.ofFinite σ.I
  have : IsIso σ.π := hq.isIso i
  let eI : Fin (Fintype.card σ.I) ≃ σ.I := (Fintype.equivFin σ.I).symm
  refine ⟨V.obj.left, V.obj.hom, V.property, ⟨⟨w, hwV₀⟩, ?_⟩, ?_⟩
  · have hW : B.inclusion.map W.obj.hom = B.inclusion.map g.hom.left := by
      simpa [SmallEtale.final] using (congrArg (fun k => B.inclusion.map k) (Over.w g.hom)).symm
    change (B.inclusion.map W.obj.hom).base (V₀.ι.base ⟨w, hwV₀⟩) = x
    rw [hW]
    exact hw
  · exact isConstructibleAbelianSheaf_pullback_kernel_frobenius_sub_one B p S hS E F hF V
      (isInCharacteristic_of_hom (B.inclusion.map V.obj.hom) p hchar) _
      (fun j => (SheafOfModules.ιFree (eI j) ≫ σ.π).val.app (op (Over.mk (jV ≫ g')))
        (1 : (SmallEtale.structureSheaf B S hS).obj.obj (op V)))
      (bijective_sum_smul_map_generatingSections B S hS E σ (jV ≫ g') eI)

open Stacks.Frobenius in
/-- Let `p` be a prime, let `S` be a scheme over `𝔽_p`, let `E` be a finite locally free module on
the small étale site of `S` and let `F : E ⟶ E` be a morphism of abelian sheaves with
`F (a • e) = a ^ p • F e` for local sections `a` of the structure sheaf and `e` of `E`. Then the
cokernel of `F - 1` is zero and the kernel of `F - 1` is a constructible abelian sheaf.

The kernel is read in the coefficient universe of the constructibility predicate, one above that
of `E`, through the universe lift of abelian groups. -/
@[stacks 0GKU]
theorem isZero_cokernel_and_isConstructible_kernel_frobeniusSemilinear_sub_id
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) (hS : B.Contains S)
    (E : SheafOfModules.{u} (SmallEtale.structureSheaf B S hS))
    [SheafOfModules.IsFiniteLocallyFree E]
    (hchar : IsInCharacteristic S p)
    (F : ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E) ⟶
      ((SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj E))
    (hF : ∀ (U : SmallEtale B S hS)
      (a : (SmallEtale.structureSheaf B S hS).obj.obj (op U))
      (e : E.val.obj (op U)),
      SheafOfModules.sectionsAddHom F (op U) (a • e) =
        a ^ p • SheafOfModules.sectionsAddHom F (op U) e) :
    IsZero (cokernel (F - 𝟙 _)) ∧
      IsConstructibleAbelianSheaf B (B.obj S hS)
        ((sheafCompose (SmallEtale.topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (kernel (F - 𝟙 _))) := by
  have := epi_frobeniusSemilinear_sub_id p B S hS E hchar F hF
  exact ⟨isZero_cokernel_of_epi _,
    isConstructibleAbelianSheaf_kernel_frobeniusSemilinear_sub_id B p S hS E hchar F hF⟩

end AlgebraicGeometry

end
