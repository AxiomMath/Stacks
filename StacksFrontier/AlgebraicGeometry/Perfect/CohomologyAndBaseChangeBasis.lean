module

public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic

/-!
# Cohomology and base change near a fibre without higher cohomology, as a basis of sections

Let `p₀ : Y₀ ⟶ P₀` be proper and flat over an affine locally Noetherian scheme `P₀`, let `F` be an
invertible `𝒪_{Y₀}`-module, and let `y₀ ∈ P₀` be a point over which the fibre has no cohomology of
`F` in positive degrees. Then there are `g ∈ Γ(P₀, 𝒪)` with `y₀ ∈ D(g)` and global sections
`e₁, …, eₙ` of `F` such that, for every affine scheme `T'` mapping into `D(g)` and every cartesian
square

```
Y' --g'--> Y₀
|p'        |p₀
T' --h-->  P₀
```

the pullbacks `g'^* eᵢ` form a basis of `Γ(Y', g'^* F)` over `Γ(T', 𝒪)`.

## Main results

* `exists_basis_of_isBaseChange_of_isBaseChange`: if `A' ⊗[A] M ≅ N₁` and `B ⊗[A] M ≅ N₂` for
  `A ⟶ A' ⟶ B`, a basis of `N₁` over `A'` consisting of images of elements of `M` has images
  forming a basis of `N₂` over `B`.
* `exists_basis_eq_of_isBaseChange_away`: a basis of a localisation `M_g` can be rescaled by units
  into a basis consisting of images of elements of `M`.
* `exists_basicOpen_bijective_sum_pullbackGlobalSections`: the sections `e₁, …, eₙ` of `F` above,
  whose pullbacks form a basis of `Γ(Y', g'^* F)` over `Γ(T', 𝒪)` for every cartesian square over
  an affine `T'` mapping into `D(g)`.

## References

* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

/-- **Base change of a basis of a localisation.** If `A' ⊗_A M ≅ N₁` and `B ⊗_A M ≅ N₂` for
`A ⟶ A' ⟶ B`, and the images in `N₁` of `m : ι → M` form a basis over `A'`, then their images in
`N₂` form a basis over `B`. -/
theorem exists_basis_of_isBaseChange_of_isBaseChange {A A' B M N₁ N₂ : Type*} {_ : CommRing A}
    {_ : CommRing A'} {_ : CommRing B} {_ : Algebra A A'} {_ : Algebra A' B} {_ : Algebra A B}
    (_ : IsScalarTower A A' B)
    {_ : AddCommGroup M} {_ : Module A M} {_ : AddCommGroup N₁} {_ : Module A N₁} {_ : Module A' N₁}
    {_ : IsScalarTower A A' N₁} {_ : AddCommGroup N₂} {_ : Module A N₂} {_ : Module B N₂}
    {_ : IsScalarTower A B N₂}
    {φ₁ : M →ₗ[A] N₁} (h₁ : IsBaseChange A' φ₁) {φ₂ : M →ₗ[A] N₂} (h₂ : IsBaseChange B φ₂)
    {ι : Type*} (b : Module.Basis ι A' N₁) (m : ι → M) (hm : ∀ i, b i = φ₁ (m i)) :
    ∃ b' : Module.Basis ι B N₂, ∀ i, b' i = φ₂ (m i) := by
  let b₁ : Module.Basis ι A' (A' ⊗[A] M) := b.map h₁.equiv.symm
  let b₂ : Module.Basis ι B (B ⊗[A'] (A' ⊗[A] M)) := Algebra.TensorProduct.basis B b₁
  let b₃ : Module.Basis ι B N₂ :=
    b₂.map ((AlgebraTensorModule.cancelBaseChange A A' B B M).trans h₂.equiv)
  refine ⟨b₃, fun i => ?_⟩
  have h1 : b₁ i = 1 ⊗ₜ m i := by
    show h₁.equiv.symm (b i) = _
    rw [hm, LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
  show h₂.equiv (AlgebraTensorModule.cancelBaseChange A A' B B M (b₂ i)) = _
  rw [Algebra.TensorProduct.basis_apply, h1, AlgebraTensorModule.cancelBaseChange_tmul,
    IsBaseChange.equiv_tmul, one_smul, one_smul]

/-- A basis of a localisation `M_g` can be rescaled by units into a basis consisting of images of
elements of `M`. -/
theorem exists_basis_eq_of_isBaseChange_away {A A' M N : Type*} {_ : CommRing A} {_ : CommRing A'}
    {_ : Algebra A A'} (g : A) (hloc : IsLocalization.Away g A')
    {_ : AddCommGroup M} {_ : Module A M} {_ : AddCommGroup N} {_ : Module A N} {_ : Module A' N}
    {_ : IsScalarTower A A' N} {φ : M →ₗ[A] N}
    (h : IsBaseChange A' φ) {ι : Type*} (b : Module.Basis ι A' N) :
    ∃ (b' : Module.Basis ι A' N) (m : ι → M), ∀ i, b' i = φ (m i) := by
  have hlocM : IsLocalizedModule (Submonoid.powers g) φ :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) A' φ).2 h
  choose ms hms using fun i => hlocM.surj (b i)
  let m : ι → M := fun i => (ms i).1
  let s : ι → Submonoid.powers g := fun i => (ms i).2
  let u : ι → A'ˣ := fun i => (IsLocalization.map_units A' (s i)).unit
  refine ⟨b.unitsSMul u, m, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply, ← hms i]
  show (algebraMap A A' (s i : A)) • b i = (s i : A) • b i
  rw [algebraMap_smul]

/-- The structural ring map of `p' ≫ T'.isoSpec.hom` is `p'.appTop`. -/
theorem globalRingHom_comp_isoSpec_hom {Y' T' : Scheme.{u}} [IsAffine T'] (p' : Y' ⟶ T') :
    Stacks.Cech.globalRingHom (A := Γ(T', ⊤)) (p' ≫ T'.isoSpec.hom) = p'.appTop := by
  ext x
  show p'.appTop (T'.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(T', ⊤)).inv x)) = p'.appTop x
  have h : T'.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(T', ⊤)).inv x) = x :=
    (congr($(Scheme.toSpecΓ_appTop T') ((Scheme.ΓSpecIso Γ(T', ⊤)).inv x))).trans
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(T', ⊤)) x)
  rw [h]

variable {Y₀ P₀ : Scheme.{u}} (p₀ : Y₀ ⟶ P₀) [IsAffine P₀]

/-- Moving a pullback square along the isomorphism `P₀ ≅ Spec Γ(P₀, ⊤)`. -/
theorem isPullback_comp_isoSpec_hom {T' Y' : Scheme.{u}} [IsAffine T'] {h : T' ⟶ P₀}
    {p' : Y' ⟶ T'} {g' : Y' ⟶ Y₀} (hsq : IsPullback g' p' p₀ h) :
    IsPullback g' (p' ≫ T'.isoSpec.hom) (p₀ ≫ P₀.isoSpec.hom) (Spec.map h.appTop) := by
  refine hsq.paste_vert ?_
  refine IsPullback.of_vert_isIso ⟨?_⟩
  exact (Scheme.isoSpec_hom_naturality h).symm

/-- **Cohomology and base change at a fibre without higher cohomology, read on global sections
over an affine base.** Let `p₀ : Y₀ ⟶ P₀` be proper and flat over an affine locally Noetherian
`P₀`, `F` an invertible module on `Y₀`, and `y₀` a point whose fibres have no higher cohomology of
`F`. Then there are `g` with `y₀ ∈ D(g)` and global sections `e₁, …, eₙ` of `F` whose pullbacks
form a basis of the global sections of the pullback of `F`, over every affine `T'` mapping into
`D(g)` and every cartesian square over it. -/
theorem exists_basicOpen_bijective_sum_pullbackGlobalSections [IsLocallyNoetherian P₀]
    [IsProper p₀] [Flat p₀] (F : Y₀.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y₀.presheaf Y₀.ringCatSheaf.2 F] (y₀ : P₀)
    (hvan : ∀ (x : PrimeSpectrum Γ(P₀, ⊤)), P₀.isoSpec.hom y₀ = x → ∀ {Xp : Scheme.{u}}
      (fp : Xp ⟶ Spec (.of x.asIdeal.ResidueField)) (gp : Xp ⟶ Y₀),
      IsPullback gp fp p₀ (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(P₀, ⊤) x.asIdeal.ResidueField)) ≫ P₀.isoSpec.inv) →
        ∀ i : ℕ, 0 < i → Subsingleton
          (((moduleGlobalSections Xp).rightDerived i).obj ((Scheme.Modules.pullback gp).obj F))) :
    ∃ (g : Γ(P₀, ⊤)) (n : ℕ) (e : Fin n → Γ(F, ⊤)), y₀ ∈ P₀.basicOpen g ∧
      ∀ {T' Y' : Scheme.{u}} [IsAffine T'] (h : T' ⟶ P₀), Set.range h ⊆ P₀.basicOpen g →
        ∀ (p' : Y' ⟶ T') (g' : Y' ⟶ Y₀), IsPullback g' p' p₀ h →
          Function.Bijective (fun c : Fin n → Γ(T', ⊤) =>
            ∑ i, (p'.appTop (c i) : Γ(Y', ⊤)) • pullbackGlobalSections g' F (e i)) := by
  classical
  set A : CommRingCat.{u} := Γ(P₀, ⊤) with hA
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top P₀⟩
  set π : Y₀ ⟶ Spec (.of A) := p₀ ≫ P₀.isoSpec.hom with hπ
  have : IsProper π := by rw [hπ]; infer_instance
  have : Flat π := by rw [hπ]; infer_instance
  have : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian p₀
  have : F.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Y₀ F
  have hflat : IsFlatOver π.toLRSHom.toShHom F := by
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (R := Y₀.ringCatSheaf) F 1 :=
      Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Y₀ F
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := Y₀.ringCatSheaf) F :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 1
    exact AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree π F
  set x : PrimeSpectrum Γ(P₀, ⊤) := P₀.isoSpec.hom y₀ with hx
  set 𝔭 := x.asIdeal with h𝔭
  have hsq₀ := IsPullback.of_hasPullback π
    (Spec.map (CommRingCat.ofHom (algebraMap A 𝔭.ResidueField)))
  have hsq₀' : IsPullback
      (pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap A 𝔭.ResidueField))))
      (pullback.snd _ _) p₀
      (Spec.map (CommRingCat.ofHom (algebraMap A 𝔭.ResidueField)) ≫ P₀.isoSpec.inv) := by
    refine hsq₀.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) P₀.isoSpec.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [hπ]
    · simp
  obtain ⟨g, hg, n, H⟩ := exists_away_cohomologyBaseChange π F hflat 𝔭 hsq₀
    (hvan x rfl _ _ hsq₀')
  have hsq₁ := IsPullback.of_hasPullback π (Spec.map (CommRingCat.ofHom
    ((RingHom.id (Localization.Away g)).comp (algebraMap A (Localization.Away g)))))
  obtain ⟨-, hBC₁, ⟨b₁⟩⟩ := H (RingHom.id _) hsq₁
  have hloc : @IsLocalization.Away A _ g (Localization.Away g) _
      ((RingHom.id (Localization.Away g)).comp (algebraMap A (Localization.Away g))).toAlgebra := by
    convert (inferInstance : IsLocalization.Away g (Localization.Away g))
    exact Algebra.algebra_ext _ _ fun _ => rfl
  obtain ⟨b₁', m, hm⟩ := exists_basis_eq_of_isBaseChange_away g hloc hBC₁ b₁
  refine ⟨g, n, m, ?_, fun {T' Y'} _ h hrange p' g' hsq => ?_⟩
  · have h1 := Scheme.toSpecΓ_preimage_basicOpen P₀ g
    have h2 : y₀ ∈ P₀.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen g := hg
    rw [h1] at h2
    exact h2
  have hunit : IsUnit (h.appTop g) := by
    refine RingedSpace.isUnit_of_isUnit_germ _ ⊤ _ fun t _ => ?_
    have ht : t ∈ T'.basicOpen (h.appTop g) := by
      rw [← Scheme.preimage_basicOpen_top]
      exact hrange ⟨t, rfl⟩
    exact (T'.mem_basicOpen_top _ t).1 ht
  set ψ : Localization.Away g →+* Γ(T', ⊤) := IsLocalization.Away.lift g hunit with hψdef
  have hψ : ψ.comp (algebraMap A (Localization.Away g)) = h.appTop.hom :=
    IsLocalization.Away.lift_comp g hunit
  have hsq' : IsPullback g' (p' ≫ T'.isoSpec.hom) π
      (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap A (Localization.Away g))))) := by
    rw [hψ]
    exact isPullback_comp_isoSpec_hom p₀ hsq
  obtain ⟨-, hBC₂, -⟩ := H ψ hsq'
  have htower : @IsScalarTower A (Localization.Away g) Γ(T', ⊤)
      ((RingHom.id (Localization.Away g)).comp
        (algebraMap A (Localization.Away g))).toAlgebra.toSMul
      ψ.toAlgebra.toSMul
      (ψ.comp (algebraMap A (Localization.Away g))).toAlgebra.toSMul := by
    let := ψ.toAlgebra
    let := ((RingHom.id (Localization.Away g)).comp (algebraMap A (Localization.Away g))).toAlgebra
    let := (ψ.comp (algebraMap A (Localization.Away g))).toAlgebra
    exact IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨b₂, hb₂⟩ := exists_basis_of_isBaseChange_of_isBaseChange htower hBC₁ hBC₂ b₁' m hm
  let := Stacks.Cech.sectionsModule (p' ≫ T'.isoSpec.hom) ((Scheme.Modules.pullback g').obj F)
    (g' ⁻¹ᵁ ⊤)
  have hfun : (fun c : Fin n → Γ(T', ⊤) =>
      ∑ i, (p'.appTop (c i) : Γ(Y', ⊤)) • pullbackGlobalSections g' F (m i)) =
      fun c => b₂.equivFun.symm c := by
    funext c
    rw [Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb₂ i, pullbackSectionsBaseₗ_top_apply]
    show _ = (Stacks.Cech.baseRingHom (p' ≫ T'.isoSpec.hom) (g' ⁻¹ᵁ ⊤)).hom (c i) •
      (pullbackSectionHom g' F ⊤ (g' ⁻¹ᵁ ⊤) le_rfl (m i) :
        Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ ⊤))
    have hb : Stacks.Cech.baseRingHom (p' ≫ T'.isoSpec.hom) (g' ⁻¹ᵁ ⊤) = p'.appTop := by
      rw [Stacks.Cech.baseRingHom, globalRingHom_comp_isoSpec_hom]
      ext x
      show (Y'.presheaf.map (𝟙 (op ⊤))) (p'.appTop x) = _
      rw [Y'.presheaf.map_id]
      rfl
    rw [hb]
    congr 1
  rw [hfun]
  exact b₂.equivFun.symm.bijective

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
