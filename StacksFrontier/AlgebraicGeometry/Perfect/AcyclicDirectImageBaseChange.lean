module

public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeAcyclic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.MateComparison
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.Reduction
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Corner
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.ModuleIsoFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Base change for the direct image of a flat module without higher cohomology

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` proper, and let `ℱ` be a quasi-coherent `𝒪_X`-module,
flat over `S`, with `Hⁱ(f⁻¹V, ℱ) = 0` for every affine open `V ⊆ S` and every `i > 0`. Then the
degree-zero base-change morphism `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is an isomorphism. No Noetherian
hypothesis is made, and `g` is arbitrary.

Over affine bases `S = Spec A`, `S' = Spec B` both sides are quasi-coherent, so it suffices to
compare global sections; there the source is `B ⊗_A Γ(X, ℱ)` because `f_* ℱ` is quasi-coherent,
and the target is `B ⊗_A Γ(X, ℱ)` by the non-Noetherian cohomology and base change of
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.cohomologyBaseChange_of_vanishing`. The
comparison carries pulled-back sections to pulled-back sections, hence is bijective.

## Main results

* `Stacks.AlgebraicGeometry.AcyclicDirectImageBaseChange.isIso_pushforwardBaseChange_spec`: the
  case `S = Spec A`, `S' = Spec B`.
* `Stacks.AlgebraicGeometry.AcyclicDirectImageBaseChange.isIso_baseChangeNatTrans_of_isAffine`:
  the case of affine `S` and `S'`.
* `Stacks.AlgebraicGeometry.AcyclicDirectImageBaseChange.isIso_baseChangeNatTrans_of_acyclic`:
  the general statement. Invertibility is local on `S'`, and over an affine open `W ⊆ S'` lying
  over an affine open `V ⊆ S` the square restricts to one with affine bases, exactly as in
  `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.isIso_baseChangeNatTrans_of_affineCase`
  (whose affine morphism hypothesis is used there only to make the corners affine).

No Stacks tag is attached; this is the step of the proof of [Stacks, Tag 0DPA] (through
[Stacks, Tag 0B9X]) that makes the direct image of the `m`-th twist of a member of `Quot^P`
commute with base change.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.AcyclicDirectImageBaseChange

open Stacks.Cech Stacks.AlgebraicGeometry.ProperFlatGlobalSections
  Stacks.AlgebraicGeometry.FlatBaseChange

section Affine

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The restriction map of the structure presheaf from `⊤` to `⊤` is the identity. -/
private theorem presheaf_map_homOfLE_top (X : Scheme.{u}) :
    X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- The structural ring map of the identity of `Spec A` to its global sections is invertible. -/
theorem isIso_baseRingHom_id_top (A : Type u) [CommRing A] :
    IsIso (baseRingHom (𝟙 (Spec (.of A))) ⊤) := by
  rw [baseRingHom, globalRingHom, presheaf_map_homOfLE_top, Category.comp_id,
    Scheme.Hom.id_appTop]
  exact @IsIso.comp_isIso _ _ _ _ _ (toSpecΓ _) (𝟙 _) (isIso_toSpecΓ _) inferInstance

/-- The structural ring map of `f' : X' ⟶ Spec B` to the global sections of `X'` is the map on
global sections of `f'` after the structural map of the identity of `Spec B`. -/
theorem baseRingHom_pushforward_apply {R : Type u} [CommRing R] {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (.of R)) (b : R) :
    (f'.app ⊤).hom ((baseRingHom (𝟙 (Spec (.of R))) ⊤).hom b) =
      (baseRingHom f' ⊤).hom b := by
  simp only [baseRingHom, globalRingHom, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [presheaf_map_homOfLE_top, presheaf_map_homOfLE_top]
  rfl

/-- Over `Spec A`, the `A`-module structure on the global sections of a direct image, through the
identity of `Spec A`, is the one on the global sections of the module itself. -/
theorem sectionsModule_pushforward {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (F : X.Modules) :
    (sectionsModule (𝟙 (Spec (.of A))) ((Scheme.Modules.pushforward f).obj F) ⊤ :
        Module A Γ((Scheme.Modules.pushforward f).obj F, (⊤ : (Spec (.of A)).Opens))) =
      (sectionsModule f F ⊤ : Module A Γ(F, (⊤ : X.Opens))) :=
  Module.ext <| funext fun a => funext fun x : Γ(F, (⊤ : X.Opens)) =>
    congrArg (fun s : Γ(X, (⊤ : X.Opens)) => s • x) (baseRingHom_pushforward_apply f a)

/-- The structural ring maps of the identities of `Spec A` and `Spec B` on global sections form a
pushout square with `φ` and the map on global sections of `Spec.map φ`. -/
private theorem isPushout_baseRingHom_spec :
    IsPushout (baseRingHom (𝟙 (Spec (.of A))) ⊤) (CommRingCat.ofHom φ)
      ((Spec.map (CommRingCat.ofHom φ)).app ⊤)
      (baseRingHom (𝟙 (Spec (.of B))) (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)) :=
  have := isIso_baseRingHom_id_top A
  have : IsIso (baseRingHom (𝟙 (Spec (.of B))) (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)) :=
    isIso_baseRingHom_id_top B
  IsPushout.of_horiz_isIso ⟨baseRingHom_comp_app _ _ _ _ IsPullback.of_id_snd ⊤⟩

/-- Over `Spec.map φ : Spec B ⟶ Spec A`, for `f` proper and a quasi-coherent `ℱ` flat over `A`
with `Hⁱ(X, ℱ) = 0` for `i > 0`, the base-change morphism is bijective on global sections. -/
private theorem bijective_pushforwardBaseChange_app_top_spec {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (H : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ))) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections X).rightDerived i).obj F)) :
    Function.Bijective ((pushforwardBaseChange H.w F).app ⊤) := by
  have : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs f F
  let : Algebra A B := φ.toAlgebra
  obtain ⟨-, hbc₂⟩ := cohomologyBaseChange_of_vanishing f F hflat hvan φ H
  have hbc₁ := isBaseChange_pullbackSectionsBaseₗ (Spec.map (CommRingCat.ofHom φ))
    ((Scheme.Modules.pushforward f).obj F) φ (𝟙 _) (𝟙 _)
    (baseRingHom_comp_app _ _ _ _ IsPullback.of_id_snd)
    (isAffineOpen_top (Spec (.of A))) (isAffineOpen_top (Spec (.of B)))
    (isPushout_baseRingHom_spec φ)
  let := sectionsModule (𝟙 (Spec (.of B)))
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj
      ((Scheme.Modules.pushforward f).obj F)) (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)
  let := sectionsModule f' ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ ⊤)
  let := baseSectionsModule g' F φ f' (g' ⁻¹ᵁ ⊤)
  let := isScalarTowerBaseSections g' F φ f' (g' ⁻¹ᵁ ⊤)
  let := baseSectionsModule (Spec.map (CommRingCat.ofHom φ))
    ((Scheme.Modules.pushforward f).obj F) φ (𝟙 (Spec (.of B)))
    (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)
  let := isScalarTowerBaseSections (Spec.map (CommRingCat.ofHom φ))
    ((Scheme.Modules.pushforward f).obj F) φ (𝟙 (Spec (.of B)))
    (Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤)
  let := sectionsModule f F ⊤
  obtain ⟨e₁, h₁⟩ : ∃ e : B ⊗[A] Γ(F, (⊤ : X.Opens)) ≃ₗ[B]
        Γ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj
          ((Scheme.Modules.pushforward f).obj F), Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤),
      ∀ (b : B) (a : Γ(F, (⊤ : X.Opens))), e (b ⊗ₜ[A] a) =
        b • pullbackSections (Spec.map (CommRingCat.ofHom φ))
          ((Scheme.Modules.pushforward f).obj F) ⊤ a :=
    exists_linearEquiv_tmul_congr
      (iM := sectionsModule (𝟙 (Spec (.of A))) ((Scheme.Modules.pushforward f).obj F) ⊤)
      (jM := sectionsModule f F ⊤) (sectionsModule_pushforward f F) rfl _
      (by
        let := sectionsModule (𝟙 (Spec (.of A))) ((Scheme.Modules.pushforward f).obj F) ⊤
        exact ⟨hbc₁.equiv, hbc₁.equiv_tmul⟩)
  let ψ : Γ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj
        ((Scheme.Modules.pushforward f).obj F), Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤) →ₗ[B]
      Γ((Scheme.Modules.pullback g').obj F, g' ⁻¹ᵁ ⊤) :=
    { toFun := fun y => (pushforwardBaseChange H.w F).app ⊤ y
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun b y => by
        refine (Scheme.Modules.Hom.app_smul (pushforwardBaseChange H.w F)
          ((baseRingHom (𝟙 (Spec (.of B))) ⊤).hom b) y).trans ?_
        exact congrArg (fun s : Γ(X', (⊤ : X'.Opens)) =>
          s • (show Γ((Scheme.Modules.pullback g').obj F, (⊤ : X'.Opens)) from
            (pushforwardBaseChange H.w F).app ⊤ y))
          (baseRingHom_pushforward_apply f' b) }
  exact bijective_of_tmul_normalisation e₁ h₁ hbc₂.equiv hbc₂.equiv_tmul ψ
    (pushforwardBaseChange_app_top_unit H.w F)

/-- **Cohomology and base change in degree zero over an affine base, without a Noetherian
hypothesis.** For a cartesian square over `Spec.map φ : Spec B ⟶ Spec A` with `f` proper and a
quasi-coherent `ℱ` flat over `A` with `Hⁱ(X, ℱ) = 0` for `i > 0`, the base-change morphism
`g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is an isomorphism. -/
theorem isIso_pushforwardBaseChange_spec {X X' : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (H : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ))) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections X).rightDerived i).obj F)) :
    IsIso (pushforwardBaseChange H.w F) := by
  have := isQuasicoherent_pullback_pushforward (Spec.map (CommRingCat.ofHom φ)) f F
  have := isQuasicoherent_pushforward_pullback H F
  exact isIso_of_bijective_app_top _
    (bijective_pushforwardBaseChange_app_top_spec φ H F hflat hvan)

end Affine

section Global

open Stacks.AlgebraicGeometry.AffineBaseChangeLocality

/-- Vanishing of a cohomology module only depends on the isomorphism class of the module. -/
theorem subsingleton_rightDerived_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (i : ℕ)
    (h : Subsingleton (((moduleGlobalSections X).rightDerived i).obj F)) :
    Subsingleton (((moduleGlobalSections X).rightDerived i).obj G) :=
  (((moduleGlobalSections X).rightDerived i).mapIso e).toLinearEquiv.toEquiv.symm.subsingleton

/-- **Cohomology and base change in degree zero over affine bases.** For a cartesian square with
`S` and `S'` affine, `f` proper and `ℱ` quasi-coherent, flat over `S`, with `Hⁱ(X, ℱ) = 0` for
`i > 0`, the base-change morphism `g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is an isomorphism. -/
theorem isIso_baseChangeNatTrans_of_isAffine {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} [IsAffine S] [IsAffine S']
    (h : IsPullback g' f' f g) [IsProper f] (F : X.Modules) [F.IsQuasicoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections X).rightDerived i).obj F)) :
    IsIso ((AffinePushforward.baseChangeNatTrans h.w).app F) := by
  let φ : Γ(S, ⊤) →+* Γ(S', ⊤) := (Spec.preimage (S'.isoSpec.inv ≫ g ≫ S.isoSpec.hom)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = S'.isoSpec.inv ≫ g ≫ S.isoSpec.hom := by
    simp only [φ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have H₂ : IsPullback g' (f' ≫ S'.isoSpec.hom) (f ≫ S.isoSpec.hom)
      (Spec.map (CommRingCat.ofHom φ)) :=
    h.of_iso (Iso.refl _) (Iso.refl _) S'.isoSpec S.isoSpec (by simp) (by simp) (by simp)
      (by rw [hφ]; simp)
  refine AffineBaseChangeIso.isIso_baseChangeNatTrans_of_cornerIso h.w H₂.w (a := 𝟙 X') (b := 𝟙 X)
    (c := S'.isoSpec.hom) (d := S.isoSpec.inv) (by simp) (by simp) (by simp)
    (by rw [hφ]; simp) F ?_
  rw [Stacks.AlgebraicGeometry.FlatBaseChange.baseChangeNatTrans_app_eq_pushforwardBaseChange]
  have : ((Scheme.Modules.pullback (𝟙 X)).obj F).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback (𝟙 X) F
  exact isIso_pushforwardBaseChange_spec φ H₂ _
    (isFlatOver_of_moduleIso _ ((Scheme.Modules.pullbackId X).app F).symm
      (isFlatOver_comp_iso f S.isoSpec F hflat))
    (fun i hi => subsingleton_rightDerived_of_iso ((Scheme.Modules.pullbackId X).app F).symm i
      (hvan i hi))

/-- In a commutative square, the preimage of an open `W ⊆ S'` lying over `V ⊆ S` lies over the
preimage of `V`. -/
private theorem preimage_le_preimage_of_comm {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) {V : S.Opens} {W : S'.Opens}
    (hgW : W ≤ g ⁻¹ᵁ V) : f' ⁻¹ᵁ W ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
  have e : (f' ≫ g) ⁻¹ᵁ V = (g' ≫ f) ⁻¹ᵁ V := by rw [w]
  simp only [Scheme.Hom.comp_preimage] at e
  rw [← e]
  exact leOfHom ((Opens.map f'.base).map (homOfLE hgW))

/-- Restricting `f'` to the preimage of an open `W ⊆ S'` gives a cartesian square over `f` and
`W.ι ≫ g`. -/
private theorem isPullback_ι_comp_morphismRestrict {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (h : IsPullback g' f' f g) (W : S'.Opens) :
    IsPullback ((f' ⁻¹ᵁ W).ι ≫ g') (f' ∣_ W) f (W.ι ≫ g) :=
  (isPullback_morphismRestrict f' W).flip.paste_horiz h

/-- A cartesian square restricts to a cartesian square over opens `W ⊆ g⁻¹ V`. -/
private theorem isPullback_resLE_morphismRestrict {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (h : IsPullback g' f' f g) {V : S.Opens}
    {W : S'.Opens} (hgW : W ≤ g ⁻¹ᵁ V) :
    IsPullback (g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ W) (preimage_le_preimage_of_comm h.w hgW))
      (f' ∣_ W) (f ∣_ V) (g.resLE V W hgW) := by
  have htop := Scheme.Hom.resLE_comp_ι g' (preimage_le_preimage_of_comm h.w hgW)
  have hbase := Scheme.Hom.resLE_comp_ι g hgW
  have hBig : IsPullback (g'.resLE _ _ (preimage_le_preimage_of_comm h.w hgW) ≫ (f ⁻¹ᵁ V).ι)
      (f' ∣_ W) f (g.resLE V W hgW ≫ V.ι) := by
    rw [htop, hbase]
    exact isPullback_ι_comp_morphismRestrict h W
  refine hBig.of_right ?_ (isPullback_morphismRestrict f V).flip
  rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι, hbase,
    ← Category.assoc, htop, Category.assoc, h.w, ← Category.assoc,
    morphismRestrict_ι_assoc, Category.assoc]

/-- **Cohomology and base change in degree zero for a flat module without higher cohomology.**
Let `X' ⟶ X` over `g : S' ⟶ S` be a cartesian square with `f : X ⟶ S` proper, and let `ℱ` be a
quasi-coherent `𝒪_X`-module, flat over `S`, whose restriction to the inverse image of every
affine open `V ⊆ S` has no cohomology in positive degrees. Then the base-change morphism
`g^* f_* ℱ ⟶ f'_* (g')^* ℱ` is an isomorphism; `g` is arbitrary and nothing is Noetherian. -/
theorem isIso_baseChangeNatTrans_of_acyclic {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (h : IsPullback g' f' f g) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hvan : ∀ V : S.Opens, IsAffineOpen V → ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections (f ⁻¹ᵁ V)).rightDerived i).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F))) :
    IsIso ((AffinePushforward.baseChangeNatTrans h.w).app F) := by
  have hU := S'.isBasis_affineOpens.isOpenCover_mem_and_le
    ((S.isBasis_affineOpens).isOpenCover.comap g.base.hom)
  refine AffineBaseChange.isIso_of_isIso_restrict _ _ hU (fun WV ↦ ?_)
  obtain ⟨⟨W₀, V₀⟩, hWaff, hle⟩ := WV
  set W : S'.Opens := W₀
  set V : S.Opens := (V₀ : S.Opens)
  have hVa : IsAffineOpen V := V₀.2
  have hgW : W ≤ g ⁻¹ᵁ V := hle
  have iV : IsAffine V.toScheme := hVa
  have iW : IsAffine W.toScheme := hWaff
  have hle2 : (f' ⁻¹ᵁ W) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := preimage_le_preimage_of_comm h.w hgW
  let gV : W.toScheme ⟶ V.toScheme := g.resLE V W hgW
  let t : (f' ⁻¹ᵁ W).toScheme ⟶ (f ⁻¹ᵁ V).toScheme := g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ W) hle2
  have hfVpull : IsPullback (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι := (isPullback_morphismRestrict f V).flip
  have hBig : IsPullback ((f' ⁻¹ᵁ W).ι ≫ g') (f' ∣_ W) f (W.ι ≫ g) :=
    isPullback_ι_comp_morphismRestrict h W
  have htop : t ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ W).ι ≫ g' := Scheme.Hom.resLE_comp_ι g' hle2
  have hbase : gV ≫ V.ι = W.ι ≫ g := Scheme.Hom.resLE_comp_ι g hgW
  have hSmall : IsPullback t (f' ∣_ W) (f ∣_ V) gV := isPullback_resLE_morphismRestrict h hgW
  have hBig2 : IsPullback (t ≫ (f ⁻¹ᵁ V).ι) (f' ∣_ W) f (gV ≫ V.ι) := hSmall.paste_horiz hfVpull
  have : IsProper (f ∣_ V) := MorphismProperty.of_isPullback hfVpull inferInstance
  have : ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F).IsQuasicoherent :=
    AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion (f ⁻¹ᵁ V).ι F
  have hflatV : IsFlatOver (f ∣_ V).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F) :=
    isFlatOver_of_moduleIso _
      ((Stacks.ProjectiveBundleQuotients.pullbackIso (f ⁻¹ᵁ V).ι).app F).symm
      (@modulePullback_isFlatOver _ _ _ _ _ _ _ _ hfVpull F ‹_› hflat)
  have := AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f V F
  have hStep1 : IsIso ((AffinePushforward.baseChangeNatTrans hBig2.w).app F) :=
    AffineBaseChangeLocality.isIso_baseChangeNatTrans_vcomp hSmall.w
      (AffineBaseChange.restrictSquare f V) hBig2.w F
      (Functor.map_isIso _ _)
      (isIso_baseChangeNatTrans_of_isAffine hSmall _ hflatV (hvan V hVa))
  have hStep2 : IsIso ((AffinePushforward.baseChangeNatTrans hBig.w).app F) :=
    AffineBaseChangeLocality.isIso_baseChangeNatTrans_congr htop hbase hBig2.w hBig.w F hStep1
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback W.ι) _).mpr
    (AffineBaseChangeLocality.isIso_map_baseChangeNatTrans_of_vcomp
      (AffineBaseChange.restrictSquare f' W) h.w hBig.w F
      (AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f' W _) hStep2)

end Global

end Stacks.AlgebraicGeometry.AcyclicDirectImageBaseChange

end
