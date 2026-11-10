module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TrivialNearFibre
public import StacksFrontier.AlgebraicGeometry.PicardGroup.DescentFromLocalGenerators
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.DegreeZero

/-!
# Invertible modules trivial on the fibres of a projective space bundle

Let `k` be an algebraically closed field, `P` a scheme locally of finite type over `k` and
`f : H ⟶ P` a morphism which is Zariski-locally on `P` the projective space `ℙᵐ`
(`Stacks.ProjectiveBundle.IsLocallyProjectiveSpace`). An invertible `𝒪_H`-module `𝒩` which is
trivial on the fibre of `f` over every `k`-rational point of `P` is the pullback `f^*ℳ` of an
invertible `𝒪_P`-module `ℳ`. In the proof of Stacks 0FH9 this is the step attributed to the
projective space bundle formula (Stacks 02TX), for the morphism `Sⁿ(X) ⟶ Pic^n_{X/k}`.

## The argument

Over a chart `V` with `f⁻¹V ≅ ℙᵐ_V`, an affine open `U = Spec R ⊆ V` gives the cartesian square
`ℙᵐ_R ⟶ H` over `Spec R ⟶ P` (`Stacks.ProjectiveBundle.exists_isPullback_fromSpec`). Every point
of `U` specializes to a closed point `𝔪`, which is `k`-rational because `k` is algebraically
closed and `R` is of finite type over `k`, so `𝒩` is trivial on the fibre `ℙᵐ_{κ(𝔪)}`
(`Stacks.ProjectiveBundle.nonempty_pullback_iso_unit_of_isTrivial_fibres`); by cohomology and
base change it is then trivial over `π⁻¹(D(g))` for some `g ∉ 𝔪`
(`Stacks.ProjectiveBundle.exists_generatorSections_preimage_basicOpen`), and `D(g)` contains the
point. So `𝒩` has a generating section over the preimage of a neighbourhood of every point of
`P`. Over a chart `f_*𝒪_H = 𝒪_P`
(`Stacks.ProjectiveBundle.bijective_app_of_isoProjectiveSpaceOver`), so the transition units of
these generators come from units on `P`, and `𝒩` descends
(`Stacks.PicardGroup.exists_pullbackPicardClass_eq_of_generators`).

The source deduces `𝒩 = f^*ℳ` from the projective space bundle formula for Chow groups. That
formula is about cycles, not invertible modules, and the argument here replaces it by the
cohomology and base change statement above; no Chow group appears.

## Main results

* `Stacks.ProjectiveBundle.generatorSectionsImage`: a generator of the restriction of a module
  along an open immersion gives a generator over the image.
* `Stacks.ProjectiveBundle.bijective_app_of_isoProjectiveSpaceOver`: `f_*𝒪_H = 𝒪_P` over a chart.
* `Stacks.ProjectiveBundle.bijective_comp_algebraMap_residueField`: closed points of a finite type
  algebra over an algebraically closed field are rational.
* `Stacks.ProjectiveBundle.exists_mem_generatorSections_preimage`: `𝒩` is trivial over the
  preimage of a neighbourhood of every point.
* `Stacks.ProjectiveBundle.exists_pullbackPicardClass_eq_of_isTrivial_fibres`: **the theorem.**

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry

universe u

namespace Stacks.ProjectiveBundle

/-! ### Generators along an open immersion -/

section OpenImmersion

variable {X Y : Scheme.{u}} (ι : X ⟶ Y) [IsOpenImmersion ι] (L : Y.Modules)

/-- The two scalar actions on the sections of the restriction along an open immersion agree,
through `AlgebraicGeometry.Scheme.Modules.restrictAppIso`. -/
lemma bijective_smul_restrictAppIso_hom {V : X.Opens} (m : Γ(L.restrict ι, V))
    (hm : Function.Bijective fun r : Γ(X, V) => (r • m : Γ(L.restrict ι, V))) :
    Function.Bijective fun r : Γ(Y, ι ''ᵁ V) =>
      (r • (L.restrictAppIso ι V).hom m : Γ(L, ι ''ᵁ V)) := by
  have hiso : Function.Bijective (L.restrictAppIso ι V).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hα : Function.Bijective (ι.appIso V).inv :=
    ConcreteCategory.bijective_of_isIso _
  have hfun : (fun r : Γ(Y, ι ''ᵁ V) => (r • (L.restrictAppIso ι V).hom m : Γ(L, ι ''ᵁ V))) ∘
        (ι.appIso V).inv =
      (L.restrictAppIso ι V).hom ∘ (fun r : Γ(X, V) => (r • m : Γ(L.restrict ι, V))) :=
    funext fun r => (Scheme.Modules.smul_restrictAppIso_hom_apply ι L V r m).symm
  have hcomp : Function.Bijective
      ((fun r : Γ(Y, ι ''ᵁ V) => (r • (L.restrictAppIso ι V).hom m : Γ(L, ι ''ᵁ V))) ∘
        (ι.appIso V).inv) := by
    rw [hfun]
    exact hiso.comp hm
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · obtain ⟨a', rfl⟩ := hα.surjective a
    obtain ⟨b', rfl⟩ := hα.surjective b
    exact congrArg _ (hcomp.injective hab)
  · obtain ⟨x, hx⟩ := hcomp.surjective y
    exact ⟨_, hx⟩

/-- **A generating section of `L|_X` over `W` gives a generating section of `L` over `ι(W)`**,
for an open immersion `ι : X ⟶ Y`. -/
def generatorSectionsImage {W : X.Opens}
    (g : GeneratorSections X.toRingedSpace (L.restrict ι) W) :
    GeneratorSections Y.toRingedSpace L (ι ''ᵁ W) := by
  refine ⟨(L.restrictAppIso ι W).hom g.val, fun V h => ?_⟩
  have himg : ι ''ᵁ (ι ⁻¹ᵁ V) = V := by
    rw [ι.image_preimage_eq_opensRange_inf, inf_eq_right]
    exact h.trans (ι.image_le_opensRange W)
  have hle : ι ⁻¹ᵁ V ≤ W := by
    have := ι.preimage_mono h
    rwa [ι.preimage_image_eq] at this
  set V' : X.Opens := ι ⁻¹ᵁ V with hV'
  clear_value V'
  clear hV'
  cases himg
  have hb := bijective_smul_restrictAppIso_hom ι L
    ((L.restrict ι).val.restrictₛₗ (homOfLE hle).op g.val) (g.property V' hle)
  rw [show (L.restrictAppIso ι V').hom
        ((L.restrict ι).val.restrictₛₗ (homOfLE hle).op g.val) =
      L.val.restrictₛₗ (homOfLE h).op ((L.restrictAppIso ι W).hom g.val) from ?_] at hb
  · exact hb
  · simp only [PresheafOfModules.restrictₛₗ_apply]
    exact Scheme.Modules.map_restrictAppIso_hom_apply ι L (homOfLE hle).op g.val

end OpenImmersion

/-! ### The structure sheaf of a projective space bundle -/

section Bundle

variable {H P : Scheme.{u}} (f : H ⟶ P)

/-- **Over a chart of a projective space bundle, `f_*𝒪_H = 𝒪_P`.** If `f⁻¹V ≅ ℙᵐ_V` over `V`,
then `f^♯ : Γ(P, A) ⟶ Γ(H, f⁻¹A)` is bijective for every open `A ⊆ V`. -/
theorem bijective_app_of_isoProjectiveSpaceOver {V : P.Opens} {m : ℕ}
    (e : (f ⁻¹ᵁ V).toScheme ≅ projectiveSpaceOver m V.toScheme)
    (he : e.hom ≫ (projectiveSpaceOver m V.toScheme ↘ V.toScheme) = f ∣_ V)
    (A : P.Opens) (hA : A ≤ V) : Function.Bijective (f.app A).hom := by
  have hc := ProjectiveSpaceHigherDirectImage.isIso_c_structureMorphism_projectiveSpaceOver
    m V.toScheme
  set A' : V.toScheme.Opens := V.ι ⁻¹ᵁ A with hA'
  have himg : V.ι ''ᵁ A' = A := by
    rw [V.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hA]
  have h1 : IsIso ((f ∣_ V).app A') := by
    rw [← he, Scheme.Hom.comp_app]
    have h3 : IsIso ((projectiveSpaceOver m V.toScheme ↘ V.toScheme).app A') :=
      NatIso.isIso_app_of_isIso _ (op A')
    have h4 : IsIso (e.hom.app ((projectiveSpaceOver m V.toScheme ↘ V.toScheme) ⁻¹ᵁ A')) :=
      have := PresheafedSpace.c_isIso_of_iso e.hom.toPshHom
      NatIso.isIso_app_of_isIso e.hom.c _
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h3 h4
  rw [morphismRestrict_app] at h1
  have h2 : IsIso (f.app (V.ι ''ᵁ A')) := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    (Functor.map_isIso _ _) h1
  rw [himg] at h2
  exact @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ (f.app A) h2

end Bundle

/-! ### Closed points of an affine chart are rational -/

/-- **The residue fields at maximal ideals of a finite type algebra over an algebraically closed
field are the field itself.** If `Spec α : Spec R ⟶ Spec k` is locally of finite type and `k` is
algebraically closed, then `k ⟶ R ⟶ κ(𝔪)` is bijective for every maximal ideal `𝔪` of `R`. -/
theorem bijective_comp_algebraMap_residueField {k : Type u} [Field k] [IsAlgClosed k]
    {R : Type u} [CommRing R] (α : k →+* R)
    (hα : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom α))) (𝔪 : Ideal R) [𝔪.IsMaximal] :
    Function.Bijective ((algebraMap R 𝔪.ResidueField).comp α) := by
  have hft : α.FiniteType := HasRingHomProperty.Spec_iff.mp hα
  have hψ : ((algebraMap R 𝔪.ResidueField).comp α).FiniteType :=
    (RingHom.FiniteType.of_surjective _ 𝔪.algebraMap_residueField_surjective).comp hft
  have hfin := RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hψ
  algebraize [(algebraMap R 𝔪.ResidueField).comp α]
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := 𝔪.ResidueField)

/-- The global functions on projective space over a field form a field. -/
theorem isField_globalSections_projectiveSpaceOver (K : Type u) [Field K] (m : ℕ) :
    IsField Γ(projectiveSpaceOver m (Spec (.of K)), ⊤) := by
  have := ProjectiveSpaceHigherDirectImage.isIso_appTop_structureMorphism_projectiveSpaceOverRing
    m (.of K)
  let e : Γ(Spec (.of K), ⊤) ≃+* Γ(projectiveSpaceOver m (Spec (.of K)), ⊤) :=
    (asIso (projectiveSpaceOverRing m (.of K) ↘ Spec (.of K)).appTop).commRingCatIsoToRingEquiv
  let e' : Γ(Spec (.of K), ⊤) ≃+* K := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  exact (e.symm.trans e').toMulEquiv.isField (Field.toIsField K)

/-- The induced morphism of projective spaces lies over the morphism of bases. -/
@[reassoc]
theorem projectiveSpaceOverMap_over (m : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) :
    projectiveSpaceOverMap m g ≫ (projectiveSpaceOver m S ↘ S) =
      (projectiveSpaceOver m S' ↘ S') ≫ g :=
  projectiveSpaceOverMap_fst m g

/-- Two points with the same image in a cartesian square of schemes come from one point of the
fibre product. -/
theorem exists_eq_of_isPullback {Q X Y Z : Scheme.{u}} {fst : Q ⟶ X} {snd : Q ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y) (hxy : f x = g y) :
    ∃ q : Q, fst q = x ∧ snd q = y :=
  Scheme.exists_preimage_of_isPullback h x y hxy

/-- **A generator on a chart gives a generator over the preimage of the image.** For a cartesian
square `φ ≫ f = π ≫ ι` with `φ` an open immersion, a generating section of `φ^*𝒩` over
`π⁻¹(D)` gives one of `𝒩` over `f⁻¹(ι(D))`. -/
def generatorSectionsPreimageImage {X H S P : Scheme.{u}} {φ : X ⟶ H} {π : X ⟶ S}
    {f : H ⟶ P} {ι : S ⟶ P} [IsOpenImmersion φ] [IsOpenImmersion ι] (hpb : IsPullback φ π f ι)
    (N : H.Modules) (D : S.Opens)
    (gen : GeneratorSections X.toRingedSpace ((Scheme.Modules.pullback φ).obj N) (π ⁻¹ᵁ D)) :
    GeneratorSections H.toRingedSpace N (f ⁻¹ᵁ (ι ''ᵁ D)) := by
  have hW : f ⁻¹ᵁ (ι ''ᵁ D) = φ ''ᵁ (π ⁻¹ᵁ D) := by
    refine Opens.ext (Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨w, hw₁, hw₂⟩ := exists_eq_of_isPullback hpb x d hdx.symm
      exact ⟨w, show π w ∈ D from hw₂ ▸ hd, hw₁⟩
    · obtain ⟨w, hw, rfl⟩ := hx
      refine ⟨π w, hw, ?_⟩
      change ι (π w) = f (φ w)
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  exact hW ▸ generatorSectionsImage φ N
    (generatorMapIso ((Scheme.Modules.restrictFunctorIsoPullback φ).app N).symm _ gen)

/-! ### Charts of a projective space bundle over affine opens -/

section Chart

variable {P H : Scheme.{u}} (f : H ⟶ P)

/-- **A chart of a projective space bundle restricts to every affine open of the base.** If
`f⁻¹V ≅ ℙᵐ_V` over `V` and `U ⊆ V` is an affine open, then `ℙᵐ_{Γ(U)} ⟶ Spec Γ(U) ⟶ P` is the
base change of `f` along `Spec Γ(U) ⟶ P`, through an open immersion `ℙᵐ_{Γ(U)} ⟶ H`. -/
theorem exists_isPullback_fromSpec {V : P.Opens} {m : ℕ}
    (e : (f ⁻¹ᵁ V).toScheme ≅ projectiveSpaceOver m V.toScheme)
    (he : e.hom ≫ (projectiveSpaceOver m V.toScheme ↘ V.toScheme) = f ∣_ V) {U : P.Opens}
    (hU : IsAffineOpen U) (hUV : U ≤ V) :
    ∃ φ : projectiveSpaceOver m (Spec Γ(P, U)) ⟶ H, IsOpenImmersion φ ∧
      IsPullback φ (projectiveSpaceOver m (Spec Γ(P, U)) ↘ Spec Γ(P, U)) f hU.fromSpec := by
  have hrange : Set.range hU.fromSpec ⊆ Set.range V.ι := by
    rw [hU.range_fromSpec, Scheme.Opens.range_ι]
    exact hUV
  let g0 : Spec Γ(P, U) ⟶ V.toScheme := IsOpenImmersion.lift V.ι hU.fromSpec hrange
  have hg0 : g0 ≫ V.ι = hU.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion g0 := by
    have : IsOpenImmersion (g0 ≫ V.ι) := hg0 ▸ inferInstance
    exact IsOpenImmersion.of_comp g0 V.ι
  have hsqV := isPullback_projectiveSpaceOverMap m g0
  have : IsOpenImmersion (projectiveSpaceOverMap m g0) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsqV.flip inferInstance
  refine ⟨projectiveSpaceOverMap m g0 ≫ e.inv ≫ (f ⁻¹ᵁ V).ι, inferInstance, ?_⟩
  have hstrV : e.inv ≫ f ∣_ V = projectiveSpaceOver m V.toScheme ↘ V.toScheme := by
    rw [← he, Iso.inv_hom_id_assoc]
  have h2 : IsPullback e.inv (projectiveSpaceOver m V.toScheme ↘ V.toScheme) (f ∣_ V) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [hstrV, Category.comp_id]⟩
  have h := (hsqV.paste_horiz h2).paste_horiz (isPullback_morphismRestrict f V).flip
  rwa [Category.comp_id, hg0, Category.assoc] at h

variable {k : Type u} [Field k] [IsAlgClosed k] (sP : P ⟶ Spec (.of k)) (m : ℕ) (N : H.Modules)
  (hN : IsInvertible H.presheaf H.ringCatIsSheaf N)

omit [IsAlgClosed k] in
/-- **The fibre of a chart over a rational point is trivial.** Let `φ : ℙᵐ_R ⟶ H` lie over
`ι : Spec R ⟶ P`, with `ι ≫ sP = Spec α` for `α : k ⟶ R`, and let `𝔪` be a maximal ideal of `R`
with `k ⟶ κ(𝔪)` bijective. If `𝒩` is trivial on the rational fibres of `f`, then `φ^*𝒩` is
trivial on the fibre `ℙᵐ_{κ(𝔪)}`. -/
theorem nonempty_pullback_iso_unit_of_isTrivial_fibres
    (hfib : ∀ (j : projectiveSpaceOverRing m (.of k) ⟶ H) (p : Spec (.of k) ⟶ P),
      p ≫ sP = 𝟙 _ → j ≫ f = (projectiveSpaceOverRing m (.of k) ↘ Spec (.of k)) ≫ p →
      pullbackPicardClass j N hN = 0)
    {R : CommRingCat.{u}} (φ : projectiveSpaceOver m (Spec R) ⟶ H) (ι : Spec R ⟶ P)
    (hφ : φ ≫ f = (projectiveSpaceOver m (Spec R) ↘ Spec R) ≫ ι) (α : .of k ⟶ R)
    (hα : Spec.map α = ι ≫ sP) (𝔪 : Ideal R) [𝔪.IsMaximal]
    (hκ : Function.Bijective ((algebraMap R 𝔪.ResidueField).comp α.hom)) :
    Nonempty ((Scheme.Modules.pullback (projectiveSpaceOverMap m
      (Spec.map (CommRingCat.ofHom (algebraMap R 𝔪.ResidueField) : R ⟶ .of 𝔪.ResidueField)))).obj
        ((modulePullback φ.toLRSHom.toShHom).obj N) ≅
      SheafOfModules.unit (projectiveSpaceOver m (Spec (.of 𝔪.ResidueField))).ringCatSheaf) := by
  set κ := 𝔪.ResidueField
  set gp : projectiveSpaceOver m (Spec (.of κ)) ⟶ projectiveSpaceOver m (Spec R) :=
    projectiveSpaceOverMap m (Spec.map (CommRingCat.ofHom (algebraMap R κ) : R ⟶ .of κ))
    with hgp
  have hL : IsInvertible (projectiveSpaceOver m (Spec R)).presheaf
      (projectiveSpaceOver m (Spec R)).ringCatIsSheaf ((modulePullback φ.toLRSHom.toShHom).obj N) :=
    Stacks.RingedSpace.modulePullback_isInvertible _ N
  set γ : k →+* κ := (algebraMap R κ).comp α.hom with hγ
  let eγ : k ≃+* κ := RingEquiv.ofBijective γ hκ
  have hγγ : Spec.map (CommRingCat.ofHom γ) ≫ Spec.map (CommRingCat.ofHom eγ.symm.toRingHom) =
      𝟙 (Spec (.of κ)) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun x => eγ.apply_symm_apply x)
  have hpt : (Spec.map (CommRingCat.ofHom eγ.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R κ) : R ⟶ .of κ) ≫ ι) ≫ sP =
        𝟙 (Spec (.of k)) := by
    rw [Category.assoc, Category.assoc, ← hα, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun x => eγ.symm_apply_apply x)
  have hj : (projectiveSpaceOverMap m (Spec.map (CommRingCat.ofHom eγ.symm.toRingHom)) ≫ gp ≫
      φ) ≫ f = (projectiveSpaceOverRing m (.of k) ↘ Spec (.of k)) ≫
        (Spec.map (CommRingCat.ofHom eγ.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R κ) : R ⟶ .of κ) ≫ ι) := by
    rw [Category.assoc, Category.assoc, hφ, hgp, projectiveSpaceOverMap_over_assoc,
      projectiveSpaceOverMap_over_assoc]
  have h0 := hfib _ _ hpt hj
  set j := projectiveSpaceOverMap m (Spec.map (CommRingCat.ofHom eγ.symm.toRingHom)) ≫ gp ≫ φ
    with hj_def
  have hcomp : projectiveSpaceOverMap m (Spec.map (CommRingCat.ofHom γ)) ≫ j = gp ≫ φ := by
    rw [hj_def, ← Category.assoc (projectiveSpaceOverMap m _), projectiveSpaceOverMap_comp,
      hγγ, projectiveSpaceOverMap_id, Category.id_comp]
  have h1 : pullbackPicardClass (gp ≫ φ) N hN = 0 := by
    refine (pullbackPicardHom_picardClass (gp ≫ φ) N hN).symm.trans ?_
    rw [← hcomp]
    exact (pullbackPicardHom_comp_apply _ _ _).trans
      ((congrArg (pullbackPicardHom _) ((pullbackPicardHom_picardClass j N hN).trans h0)).trans
        (map_zero _))
  exact (pullbackPicardClass_eq_zero_iff gp _ hL).mp
    ((pullbackPicardClass_comp gp φ N hN hL).symm.trans h1)

/-- **An invertible module trivial on the rational fibres of a projective space bundle is trivial
over the preimage of a neighbourhood of every point of a chart.** -/
theorem exists_mem_generatorSections_preimage [LocallyOfFiniteType sP]
    (hfib : ∀ (j : projectiveSpaceOverRing m (.of k) ⟶ H) (p : Spec (.of k) ⟶ P),
      p ≫ sP = 𝟙 _ → j ≫ f = (projectiveSpaceOverRing m (.of k) ↘ Spec (.of k)) ≫ p →
      pullbackPicardClass j N hN = 0)
    {V : P.Opens} (e : (f ⁻¹ᵁ V).toScheme ≅ projectiveSpaceOver m V.toScheme)
    (he : e.hom ≫ (projectiveSpaceOver m V.toScheme ↘ V.toScheme) = f ∣_ V) (y : P)
    (hy : y ∈ V) :
    ∃ W : P.Opens, y ∈ W ∧ W ≤ V ∧
      Nonempty (GeneratorSections H.toRingedSpace N (f ⁻¹ᵁ W)) := by
  obtain ⟨_, ⟨U, hU', rfl⟩, hyU, hUV⟩ := P.isBasis_affineOpens.exists_subset_of_mem_open hy V.2
  have hU : IsAffineOpen U := hU'
  obtain ⟨φ, hφo, hpb⟩ := exists_isPullback_fromSpec f e he hU hUV
  -- the `k`-algebra `Γ(U)`: Noetherian, with rational closed points
  obtain ⟨α, hα⟩ := Spec.map_surjective (hU.fromSpec ≫ sP)
  have hαft : LocallyOfFiniteType (Spec.map α) := by
    rw [hα]
    infer_instance
  have : IsNoetherianRing Γ(P, U) := by
    have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
    exact IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  -- a closed point of the chart to which `y` specializes
  set q := hU.primeIdealOf ⟨y, hyU⟩
  obtain ⟨𝔪, h𝔪, hq𝔪⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  have hκ := bijective_comp_algebraMap_residueField α.hom (by simpa using hαft) 𝔪
  -- triviality over a neighbourhood of the fibre over `𝔪`
  have := isProper_projectiveSpaceOver m (Spec Γ(P, U))
  obtain ⟨g, hg, ⟨gen⟩⟩ := exists_generatorSections_preimage_basicOpen
    (A := Γ(P, U)) (projectiveSpaceOver m (Spec Γ(P, U)) ↘ Spec Γ(P, U))
    ((modulePullback φ.toLRSHom.toShHom).obj N) (Stacks.RingedSpace.modulePullback_isInvertible _ N)
    𝔪 (isPullback_projectiveSpaceOverMap m _)
    (nonempty_pullback_iso_unit_of_isTrivial_fibres f sP m N hN hfib φ hU.fromSpec hpb.w α hα
      𝔪 hκ)
    (fun q hq => subsingleton_rightDerived_unit_projectiveSpaceOver m _ q hq)
    (isField_globalSections_projectiveSpaceOver 𝔪.ResidueField m)
  refine ⟨hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g, ?_, ?_,
    ⟨generatorSectionsPreimageImage hpb N _ gen⟩⟩
  · have hz : hU.fromSpec ⟨𝔪, h𝔪.isPrime⟩ ∈ hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen g :=
      ⟨⟨𝔪, h𝔪.isPrime⟩, (PrimeSpectrum.mem_basicOpen _ _).mpr hg, rfl⟩
    have hsp : q ⤳ (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum Γ(P, U)) :=
      (PrimeSpectrum.le_iff_specializes q ⟨𝔪, h𝔪.isPrime⟩).mp hq𝔪
    have hy' : hU.fromSpec q = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
    rw [← hy']
    exact (hsp.map hU.fromSpec.continuous).mem_open (hU.fromSpec ''ᵁ _).isOpen hz
  · rintro x ⟨d, -, rfl⟩
    exact hUV (hU.range_fromSpec ▸ Set.mem_range_self d)

end Chart

/-- **An invertible module trivial on the rational fibres of a projective space bundle is
pulled back from the base.** Let `k` be algebraically closed, `P` locally of finite type over
`k`, and `f : H ⟶ P` Zariski-locally on `P` a projective space bundle `ℙᵐ`: every point of `P`
has an open neighbourhood `V` with `f⁻¹V ≅ ℙᵐ_V` over `V`. Let `𝒩` be invertible on `H` and
trivial on the fibre over every `k`-rational point, in the form that `j^*𝒩` is trivial for every
`j : ℙᵐ_k ⟶ H` over a `k`-point `p` of `P`. Then `𝒩 ≅ f^*ℳ` for an invertible `𝒪_P`-module `ℳ`.

This is the step of the proof of Stacks 0FH9 which the source attributes to the projective
space bundle formula (Stacks 02TX). -/
theorem exists_pullbackPicardClass_eq_of_isTrivial_fibres {k : Type u} [Field k] [IsAlgClosed k]
    {P H : Scheme.{u}} (sP : P ⟶ Spec (.of k)) [LocallyOfFiniteType sP] (f : H ⟶ P) (m : ℕ)
    (hbundle : IsLocallyProjectiveSpace f m)
    (N : H.Modules) (hN : IsInvertible H.presheaf H.ringCatIsSheaf N)
    (hfib : ∀ (j : projectiveSpaceOverRing m (.of k) ⟶ H) (p : Spec (.of k) ⟶ P),
      p ≫ sP = 𝟙 _ → j ≫ f = (projectiveSpaceOverRing m (.of k) ↘ Spec (.of k)) ≫ p →
      pullbackPicardClass j N hN = 0) :
    ∃ (M : P.Modules) (hM : IsInvertible P.presheaf P.ringCatIsSheaf M),
      pullbackPicardClass f M hM = H.picardClass N hN := by
  refine Stacks.PicardGroup.exists_pullbackPicardClass_eq_of_generators f N hN fun y => ?_
  obtain ⟨V, hyV, e, he⟩ := hbundle y
  obtain ⟨W, hyW, hWV, hgen⟩ :=
    exists_mem_generatorSections_preimage f sP m N hN hfib e he y hyV
  exact ⟨W, hyW, fun A hA => bijective_app_of_isoProjectiveSpaceOver f e he A (hA.trans hWV),
    hgen⟩


end Stacks.ProjectiveBundle

end
