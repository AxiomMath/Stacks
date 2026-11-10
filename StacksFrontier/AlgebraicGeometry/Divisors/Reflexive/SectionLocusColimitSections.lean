module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ColimitSectionsQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerHartogs
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusChart
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusDivisibility
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusRestrictInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusStalkUnit
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimensionTwoOpen
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Pullback.OpenImmersionPushforwardStalkLinear

/-!
# The colimit clause of [Stacks, Tag 0EBN]

Let `X` be an integral locally Noetherian normal scheme, `ℱ` a coherent reflexive `𝒪_X`-module,
`s ∈ Γ(X, ℱ)`, and `U = AlgebraicGeometry.sectionIsomorphismOpen X F s` the open locus where `s`
trivializes the stalks of `ℱ`, with inclusion `j : U ⟶ X`. When `U` is nonempty,

`j_*𝒪_U = colim (𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯)`,

the colimit being realised by the cocone
`Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePowerSystemPushforwardCocone`.

## Main definitions

* `isColimitOfForallIsAffineOpen`: a cocone on a sequence of `𝒪_X`-modules is a colimit if over
  every affine open its legs are jointly surjective on sections and kill only sections that some
  transition map kills.

## Main results

* `cocone_ι_app_zero_app` and `cocone_ι_app_app`: the legs of the cocone on sections.
* `cocone_ι_app_unitPower`: the leg at `k` carries `unitPower F s D k` to the restriction of `1`.
* `exists_leg_app_eq_of_chart`: on an affine chart `D` with `s|_D = g e` and `U ⊓ D = D(g)`,
  every section of `j_*𝒪_U` over `D` is in the image of a leg.
* `cocone_ι_app_app_eq_zero`: the legs are injective on sections.
* `exists_leg_app_eq_of_isAffineOpen'` and `exists_map_app_eq_zero_of_cocone_ι_app_eq_zero`: the
  two conditions of the colimit criterion over an affine open.
* `nonempty_isColimit_reflexivePowerSystemPushforwardCocone`: the colimit clause of
  [Stacks, Tag 0EBN] for nonempty `U`.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive)
open Stacks.SheafOfModules.OnSpace (unitSection)

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
  [F.IsCoherent] (s : F.sections)
  [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- Restricting a section along an equality of opens and back is the identity. -/
theorem presheaf_map_eqToHom_map_eqToHom {A B : X.Opens} (h : A = B) (t : Γ(X, A)) :
    X.presheaf.map (eqToHom h).op (X.presheaf.map (eqToHom h.symm).op t) = t := by
  subst h
  simp

/-- The leg at `0` of the cocone of [Stacks, Tag 0EBN] is restriction to `U` on sections. -/
theorem cocone_ι_app_zero_app (D : X.Opens) (a : Γ(X, D)) :
    Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app 0) D a =
      (sectionIsomorphismOpen X F s).ι.app D a := by
  rw [reflexivePowerSystemPushforwardCocone_ι_app_eq_unit_comp,
    restrictReflexivePowerUnitIso_zero_hom]
  change ((sectionIsomorphismOpen X F s).ι.appIso
      ((sectionIsomorphismOpen X F s).ι ⁻¹ᵁ D)).hom.hom
      ((X.presheaf.map
        (homOfLE ((sectionIsomorphismOpen X F s).ι.image_preimage_le D)).op).hom a) =
      (sectionIsomorphismOpen X F s).ι.app D a
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- On sections over `W`, the leg at `n` is restriction to `j ''ᵁ j⁻¹ᵁ W`, whose sections are
those of `ℱ^{[n]}|_U` over `j⁻¹ᵁ W`, followed by the trivialization `ℱ^{[n]}|_U ≅ 𝒪_U`. -/
theorem cocone_ι_app_app (n : ℕ) (W : X.Opens) (η : Γ(reflexivePower F n, W)) :
    Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app n) W η =
      ((restrictReflexivePowerUnitIso F s n).hom.val.app
        (op ((sectionIsomorphismOpen X F s).ι ⁻¹ᵁ W))).hom
        ((reflexivePower F n).presheaf.map
          (homOfLE ((sectionIsomorphismOpen X F s).ι.image_preimage_le W)).op η) := by
  rw [reflexivePowerSystemPushforwardCocone_ι_app_eq_unit_comp]
  rfl

/-- The legs of the cocone are compatible with the transition maps on sections. -/
private theorem cocone_ι_app_map_app {i j : ℕ} (hij : i ≤ j) (W : X.Opens)
    (η : Γ((reflexivePowerSystem F s).obj i, W)) :
    Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app j) W
        (Scheme.Modules.Hom.app ((reflexivePowerSystem F s).map (homOfLE hij)) W η) =
      Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app i) W η :=
  congrArg (fun φ : (reflexivePowerSystem F s).obj i ⟶
      (reflexivePowerSystemPushforwardCocone F s).pt => Scheme.Modules.Hom.app φ W η)
    ((reflexivePowerSystemPushforwardCocone F s).w (homOfLE hij))

/-- The leg at `k` carries `unitPower F s D k` to the restriction of `1`. -/
theorem cocone_ι_app_unitPower (D : X.Opens) (k : ℕ) :
    Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app k) D
        (unitPower F s D k) =
      (sectionIsomorphismOpen X F s).ι.app D 1 :=
  (cocone_ι_app_map_app F s (Nat.zero_le k) D (unitSection X.toRingedSpace (op D) 1)).trans
    (cocone_ι_app_zero_app F s D 1)

omit [Nonempty (AlgebraicGeometry.sectionIsomorphismOpen X F s).toScheme] in
/-- The `𝒪_X(D)`-module structure on the sections of `j_*𝒪_U` over `D` is multiplication by the
comorphism of `j`. -/
theorem pushforwardUnit_smul (D : X.Opens) (r : Γ(X, D))
    (ξ : Γ(pushforwardUnit (sectionIsomorphismOpen X F s), D)) :
    r • ξ =
      ((sectionIsomorphismOpen X F s).ι.app D r *
        (show Γ((sectionIsomorphismOpen X F s).toScheme,
          (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ D) from ξ) :
      Γ(pushforwardUnit (sectionIsomorphismOpen X F s), D)) := rfl

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A section of a torsion free quasi-coherent module vanishing on a smaller open that contains
the generic point whenever the larger one does is zero. -/
theorem eq_zero_of_presheaf_map_eq_zero (M : X.Modules) [M.IsQuasicoherent]
    (hM : ReflexiveModules.IsTorsionFree M) {W W' : X.Opens} (h : W' ≤ W)
    (hW : genericPoint X ∈ W → genericPoint X ∈ W') (η : Γ(M, W))
    (hη : M.presheaf.map (homOfLE h).op η = 0) : η = 0 := by
  by_cases hg : genericPoint X ∈ W
  · refine injective_generic_germ_of_isTorsionFree M hM hg ?_
    rw [map_zero, ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE h) _ (hW hg), hη,
      map_zero]
  · exact (subsingleton_sections_of_notMem_genericPoint M W hg).elim _ _

/-- **The legs of the cocone of [Stacks, Tag 0EBN] are injective on sections** once `U` contains
the generic point. -/
theorem cocone_ι_app_app_eq_zero (hF : IsReflexive F) (hU : genericPoint X ∈
    sectionIsomorphismOpen X F s) (n : ℕ) (W : X.Opens) (η : Γ(reflexivePower F n, W))
    (h : Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app n) W η = 0) :
    η = 0 := by
  have hres : (reflexivePower F n).presheaf.map
      (homOfLE ((sectionIsomorphismOpen X F s).ι.image_preimage_le W)).op η = 0 := by
    have hz := (cocone_ι_app_app F s n W η).symm.trans h
    have hback := congrArg
      (fun φ => Scheme.Modules.Hom.app φ ((sectionIsomorphismOpen X F s).ι ⁻¹ᵁ W)
        ((reflexivePower F n).presheaf.map
          (homOfLE ((sectionIsomorphismOpen X F s).ι.image_preimage_le W)).op η))
      (restrictReflexivePowerUnitIso F s n).hom_inv_id
    refine hback.symm.trans ?_
    change ((restrictReflexivePowerUnitIso F s n).inv.val.app
      (op ((sectionIsomorphismOpen X F s).ι ⁻¹ᵁ W))).hom
        (((restrictReflexivePowerUnitIso F s n).hom.val.app
          (op ((sectionIsomorphismOpen X F s).ι ⁻¹ᵁ W))).hom _) = 0
    rw [hz]
    exact map_zero _
  have : _root_.SheafOfModules.IsCoherent (reflexivePower F n) :=
    isCoherent_reflexivePower' F ‹_› n
  have : (reflexivePower F n).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  exact eq_zero_of_presheaf_map_eq_zero (reflexivePower F n)
    (ReflexiveModules.isTorsionFree_of_isReflexive_of_isLocallyNoetherian _
      (isReflexive_reflexivePower F ‹_› hF n))
    ((sectionIsomorphismOpen X F s).ι.image_preimage_le W)
    (fun hg => ⟨⟨genericPoint X, hU⟩, hg, rfl⟩) η hres

/-- The image of the preimage of `Y` under the inclusion of an open `V` is `V ⊓ Y`. -/
private theorem image_preimage_ι_eq_inf {Z : Scheme.{u}} (V Y : Z.Opens) :
    V.ι ''ᵁ V.ι ⁻¹ᵁ Y = V ⊓ Y := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

/-- **The local claim**: on an affine chart `D` on which `s|_D = g e` and `U ⊓ D = D(g)`, every
section of `j_*𝒪_U` over `D` is in the image of some leg of the cocone of [Stacks, Tag 0EBN]. -/
theorem exists_leg_app_eq_of_chart (D : X.Opens) (hD : IsAffineOpen D) (e : Γ(F, D))
    (g : Γ(X, D)) (hs : s.eval (op D) = g • e)
    (hUD : sectionIsomorphismOpen X F s ⊓ D = X.basicOpen g)
    (ξ : Γ((sectionIsomorphismOpen X F s).toScheme,
      (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ D)) :
    ∃ (n : ℕ) (η : Γ(reflexivePower F n, D)),
      Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app n) D η = ξ := by
  have himg : (sectionIsomorphismOpen X F s).ι ''ᵁ (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ D =
      X.basicOpen g :=
    (image_preimage_ι_eq_inf _ D).trans hUD
  obtain ⟨m, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X D hD g
    (X.presheaf.map (eqToHom himg.symm).op
      (show Γ(X, (sectionIsomorphismOpen X F s).ι ''ᵁ
        (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ D) from ξ))
  have e1 : ∀ t : Γ(X, D), X.presheaf.map (eqToHom himg).op
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op t) =
      (sectionIsomorphismOpen X F s).ι.app D t := fun t => by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have key : (sectionIsomorphismOpen X F s).ι.app D y =
      ((sectionIsomorphismOpen X F s).ι.app D g) ^ m * ξ := by
    have h := congrArg (X.presheaf.map (eqToHom himg).op) hy
    rw [map_mul, map_pow, presheaf_map_eqToHom_map_eqToHom himg] at h
    rwa [← e1 y, ← e1 g]
  obtain ⟨b, hb⟩ := exists_unitPower_eq_pow_smul F s D e g hs m
  refine ⟨m, y • b, ?_⟩
  have hℓ : ∀ (r : Γ(X, D)) (t : Γ(reflexivePower F m, D)),
      Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app m) D (r • t) =
        ((sectionIsomorphismOpen X F s).ι.app D r *
          (show Γ((sectionIsomorphismOpen X F s).toScheme,
              (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ D) from
            Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app m) D t)) :=
    fun r t => Scheme.Modules.Hom.app_smul _ r t
  have hone : ((sectionIsomorphismOpen X F s).ι.app D g) ^ m *
      (show Γ((sectionIsomorphismOpen X F s).toScheme,
          (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ D) from
        Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app m) D b) = 1 := by
    rw [← map_pow, ← hℓ, ← hb, cocone_ι_app_unitPower, map_one]
  refine (hℓ y b).trans ?_
  rw [key, mul_assoc, mul_comm ξ, ← mul_assoc, hone, one_mul]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A morphism of `𝒪_X`-modules commutes with restriction of sections. -/
theorem hom_app_presheaf_map {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W)
    (t : Γ(M, W)) :
    Scheme.Modules.Hom.app φ W' (M.presheaf.map (homOfLE h).op t) =
      N.presheaf.map (homOfLE h).op (Scheme.Modules.Hom.app φ W t) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op t

omit [IsIntegral X] [IsNormal X] in
/-- `V ⊓ W` is quasi-compact when `W` is an affine open of a locally Noetherian scheme. -/
theorem isCompact_inf_of_isAffineOpen (V W : X.Opens) (hW : IsAffineOpen W) :
    IsCompact ((V ⊓ W : X.Opens) : Set X) := by
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hN := noetherianSpace_of_isAffineOpen W hW
  have h := (@NoetherianSpace.isCompact _ _ hN ((Subtype.val : W → X) ⁻¹' (V : Set X))).image
    continuous_subtype_val
  have hset : ((V ⊓ W : X.Opens) : Set X) =
      Subtype.val '' ((Subtype.val : W → X) ⁻¹' (V : Set X)) := by
    ext z
    simp only [Opens.coe_inf, Set.mem_inter_iff, Set.mem_image, Set.mem_preimage]
    exact ⟨fun hz => ⟨⟨z, hz.2⟩, hz.1, rfl⟩, fun hz => by
      obtain ⟨w, hwV, rfl⟩ := hz
      exact ⟨hwV, w.2⟩⟩
  rwa [hset]

/-- **Local gluing over `V ⊓ W`**: for an affine open `W` and an open `V` whose points have
arbitrarily small affine charts `D` with `s|_D = g e` and `U ⊓ D = D(g)`, the restriction to
`V ⊓ W` of a section of `j_*𝒪_U` over `W` is in the image of some leg of the cocone. -/
private theorem exists_leg_app_inf_eq_of_isAffineOpen (hF : IsReflexive F)
    (hgU : genericPoint X ∈ sectionIsomorphismOpen X F s) (V : X.Opens)
    (hchart : ∀ y ∈ V, ∀ N : X.Opens, y ∈ N → ∃ D : X.Opens, IsAffineOpen D ∧ y ∈ D ∧ D ≤ N ∧
      ∃ (e : Γ(F, D)) (g : Γ(X, D)), s.eval (op D) = g • e ∧
        sectionIsomorphismOpen X F s ⊓ D = X.basicOpen g)
    (W : X.Opens) (hW : IsAffineOpen W)
    (ξ : Γ(pushforwardUnit (sectionIsomorphismOpen X F s), W)) :
    ∃ (N : ℕ) (η' : Γ(reflexivePower F N, V ⊓ W)),
      Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app N) (V ⊓ W) η' =
        (pushforwardUnit (sectionIsomorphismOpen X F s)).presheaf.map
          (homOfLE (inf_le_right : V ⊓ W ≤ W)).op ξ := by
  choose D hDaff hyD hDle e g hse hUD using
    fun y : {y : X // y ∈ V ⊓ W} => hchart y.1 y.2.1 (V ⊓ W) y.2
  have hDW : ∀ y, D y ≤ W := fun y => (hDle y).trans inf_le_right
  choose nn ηη hηη using fun y => exists_leg_app_eq_of_chart F s (D y) (hDaff y) (e y) (g y)
    (hse y) (hUD y)
    ((pushforwardUnit (sectionIsomorphismOpen X F s)).presheaf.map (homOfLE (hDW y)).op ξ)
  obtain ⟨t, ht⟩ := (isCompact_inf_of_isAffineOpen V W hW).elim_finite_subcover
    (fun y : {y : X // y ∈ V ⊓ W} => (D y : Set X))
    (fun y => (D y).isOpen) fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hyD _⟩
  set N := t.sup nn
  have hle : ∀ i : t, nn i.1 ≤ N := fun i => Finset.le_sup i.2
  let sf : ∀ i : t, Γ(reflexivePower F N, D i.1) := fun i =>
    Scheme.Modules.Hom.app ((reflexivePowerSystem F s).map (homOfLE (hle i))) (D i.1) (ηη i.1)
  have hsf : ∀ i : t, Scheme.Modules.Hom.app
      ((reflexivePowerSystemPushforwardCocone F s).ι.app N) (D i.1) (sf i) =
      (pushforwardUnit (sectionIsomorphismOpen X F s)).presheaf.map
        (homOfLE (hDW i.1)).op ξ := fun i =>
    (cocone_ι_app_map_app F s (hle i) _ (ηη i.1)).trans (hηη i.1)
  have hPres : ∀ {A B C : X.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C)
      (z : Γ(pushforwardUnit (sectionIsomorphismOpen X F s), C)),
      (pushforwardUnit (sectionIsomorphismOpen X F s)).presheaf.map (homOfLE h₁).op
          ((pushforwardUnit (sectionIsomorphismOpen X F s)).presheaf.map (homOfLE h₂).op z) =
        (pushforwardUnit (sectionIsomorphismOpen X F s)).presheaf.map
          (homOfLE (h₁.trans h₂)).op z := fun h₁ h₂ z => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hcover : V ⊓ W ≤ iSup fun i : t => D i.1 := fun z hz => by
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hzi⟩
  have hlegres : ∀ (i : t) {A : X.Opens} (hA : A ≤ D i.1),
      Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app N) A
          ((reflexivePower F N).presheaf.map (homOfLE hA).op (sf i)) =
        (pushforwardUnit (sectionIsomorphismOpen X F s)).presheaf.map
          (homOfLE (hA.trans (hDW i.1))).op ξ := fun i A hA =>
    (hom_app_presheaf_map _ hA (sf i)).trans
      ((congrArg ((pushforwardUnit (sectionIsomorphismOpen X F s)).presheaf.map
        (homOfLE hA).op) (hsf i)).trans (hPres hA (hDW i.1) ξ))
  have hcompat : TopCat.Presheaf.IsCompatible (reflexivePower F N).presheaf
      (fun i : t => D i.1) sf := by
    intro i j
    refine sub_eq_zero.mp (cocone_ι_app_app_eq_zero F s hF hgU N (D i.1 ⊓ D j.1) _ ?_)
    refine (map_sub _ _ _).trans ?_
    rw [sub_eq_zero]
    exact (hlegres i inf_le_left).trans (hlegres j inf_le_right).symm
  obtain ⟨η', hη', -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(reflexivePower F N).presheaf, (reflexivePower F N).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i : t => D i.1) (V ⊓ W) (fun i => homOfLE (hDle i.1)) hcover sf hcompat
  refine ⟨N, η', TopCat.Sheaf.eq_of_locally_eq'
    (⟨(pushforwardUnit (sectionIsomorphismOpen X F s)).presheaf,
      (pushforwardUnit (sectionIsomorphismOpen X F s)).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i : t => D i.1) (V ⊓ W) (fun i => homOfLE (hDle i.1)) hcover _ _ fun i => ?_⟩
  exact (hom_app_presheaf_map _ (hDle i.1) η').symm.trans ((congrArg _ (hη' i)).trans
    ((hsf i).trans (hPres (hDle i.1) (inf_le_right : V ⊓ W ≤ W) ξ).symm))

/-- **The surjectivity condition of the colimit criterion over an affine open `W`**, given an open
`V` whose complement has codimension at least two and whose points have arbitrarily small affine
charts `D` with `s|_D = g e` and `U ⊓ D = D(g)`. -/
theorem exists_leg_app_eq_of_isAffineOpen (hF : IsReflexive F) (V : X.Opens)
    (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hchart : ∀ y ∈ V, ∀ N : X.Opens, y ∈ N → ∃ D : X.Opens, IsAffineOpen D ∧ y ∈ D ∧ D ≤ N ∧
      ∃ (e : Γ(F, D)) (g : Γ(X, D)), s.eval (op D) = g • e ∧
        sectionIsomorphismOpen X F s ⊓ D = X.basicOpen g)
    (W : X.Opens) (hW : IsAffineOpen W)
    (ξ : Γ(pushforwardUnit (sectionIsomorphismOpen X F s), W)) :
    ∃ (n : ℕ) (η : Γ(reflexivePower F n, W)),
      Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app n) W η = ξ := by
  have himg := image_preimage_ι_eq_inf (sectionIsomorphismOpen X F s)
  by_cases hg : genericPoint X ∈ (sectionIsomorphismOpen X F s).ι ''ᵁ
      (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ W
  swap
  · have h1 : Subsingleton Γ(SheafOfModules.unit X.ringCatSheaf,
        (sectionIsomorphismOpen X F s).ι ''ᵁ (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ W) :=
      subsingleton_sections_of_notMem_genericPoint _ _ hg
    have h2 : Subsingleton Γ(pushforwardUnit (sectionIsomorphismOpen X F s), W) := h1
    exact ⟨0, 0, @Subsingleton.elim _ h2 _ _⟩
  rw [himg] at hg
  obtain ⟨hgU, hgW⟩ := hg
  obtain ⟨N, η', hleg'⟩ := exists_leg_app_inf_eq_of_isAffineOpen F s hF hgU V hchart W hW ξ
  obtain ⟨η, hη⟩ := (bijective_resF_inf_reflexivePower F ‹_› hF V hV N W).2 η'
  refine ⟨N, η, ?_⟩
  have : Nonempty ((sectionIsomorphismOpen X F s).ι ''ᵁ
      (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ (V ⊓ W)) :=
    ⟨⟨genericPoint X, (himg (V ⊓ W)).ge
      ⟨hgU, genericPoint_mem_of_forall_two_le_codimension V hV, hgW⟩⟩⟩
  refine map_injective_of_isIntegral (X := X)
    (homOfLE (Scheme.Hom.image_mono _ (Scheme.Hom.preimage_mono _
      (inf_le_right : V ⊓ W ≤ W))) :
      (sectionIsomorphismOpen X F s).ι ''ᵁ
        (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ (V ⊓ W) ⟶
      (sectionIsomorphismOpen X F s).ι ''ᵁ
        (sectionIsomorphismOpen X F s).ι ⁻¹ᵁ W) ?_
  exact ((hom_app_presheaf_map ((reflexivePowerSystemPushforwardCocone F s).ι.app N)
    (inf_le_right : V ⊓ W ≤ W) η).symm.trans (congrArg _ hη)).trans hleg'

/-- **The kernel condition of the colimit criterion**, when `U` contains the generic point: a
section killed by a leg is killed by a transition map. -/
theorem exists_map_app_eq_zero_of_cocone_ι_app_eq_zero (hF : IsReflexive F)
    (hU : genericPoint X ∈ sectionIsomorphismOpen X F s) (W : X.Opens) (n : ℕ)
    (η : Γ(reflexivePower F n, W))
    (h : Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app n) W η = 0) :
    ∃ (m : ℕ) (hm : n ≤ m),
      Scheme.Modules.Hom.app ((reflexivePowerSystem F s).map (homOfLE hm)) W η = 0 := by
  refine ⟨n, le_rfl, ?_⟩
  rw [cocone_ι_app_app_eq_zero F s hF hU n W η h]
  exact map_zero _

/-- **A cocone on a sequence of `𝒪_X`-modules is a colimit** as soon as, over every affine open
`W`, its legs are jointly surjective on sections and kill only sections that some transition map
kills. -/
def isColimitOfForallIsAffineOpen {Y : Scheme.{u}} {D : ℕ ⥤ Y.Modules} (c : Limits.Cocone D)
    (hsurj : ∀ W : Y.Opens, IsAffineOpen W → ∀ ξ : Γ(c.pt, W),
      ∃ (n : ℕ) (η : Γ(D.obj n, W)), (c.ι.app n).app W η = ξ)
    (hker : ∀ W : Y.Opens, IsAffineOpen W → ∀ (n : ℕ) (η : Γ(D.obj n, W)),
      (c.ι.app n).app W η = 0 →
        ∃ (m : ℕ) (h : n ≤ m), (D.map (homOfLE h)).app W η = 0) :
    Limits.IsColimit c :=
  isColimitOfForallMemIsBasis c Y.isBasis_affineOpens (fun W hW => hsurj W hW) fun W hW =>
    hker W hW

/-- **The legs are jointly surjective on the sections over every affine open `W`.** -/
theorem exists_leg_app_eq_of_isAffineOpen' (hF : IsReflexive F) (W : X.Opens)
    (hW : IsAffineOpen W) (ξ : Γ(pushforwardUnit (sectionIsomorphismOpen X F s), W)) :
    ∃ (n : ℕ) (η : Γ(reflexivePower F n, W)),
      Scheme.Modules.Hom.app ((reflexivePowerSystemPushforwardCocone F s).ι.app n) W η = ξ := by
  have hgU : genericPoint X ∈ sectionIsomorphismOpen X F s :=
    genericPoint_mem_sectionIsomorphismOpen (X := X) (F := F) (s := s)
  obtain ⟨V, hVcodim, hVfree, -⟩ := exists_open_isIso_unit_forall_reflexivePower F hF
  have hinv := isInvertible_restrict_of_isFiniteLocallyFree X F s V hVfree
    ⟨genericPoint X, genericPoint_mem_of_forall_two_le_codimension V hVcodim⟩ hgU
  have hchart : ∀ y ∈ V, ∀ N : X.Opens, y ∈ N → ∃ D : X.Opens, IsAffineOpen D ∧ y ∈ D ∧
      D ≤ N ∧ ∃ (e : Γ(F, D)) (g : Γ(X, D)), s.eval (op D) = g • e ∧
        sectionIsomorphismOpen X F s ⊓ D = X.basicOpen g := by
    intro y hy N hyN
    obtain ⟨D, hDaff, hyD, hDN, e, g, hse, hloc⟩ := exists_affine_sectionLocusChart F s V hinv
      hy hyN
    exact ⟨D, hDaff, hyD, hDN, e, g, hse, le_antisymm (fun z hz => (hloc z hz.2).1 hz.1)
      fun z hz => ⟨(hloc z (X.basicOpen_le g hz)).2 hz, X.basicOpen_le g hz⟩⟩
  exact exists_leg_app_eq_of_isAffineOpen F s hF V hVcodim hchart W hW ξ

/-- **The colimit clause of [Stacks, Tag 0EBN] on a nonempty isomorphism locus**: `j_*𝒪_U` is the
colimit of `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯`, realised by `reflexivePowerSystemPushforwardCocone`. -/
theorem nonempty_isColimit_reflexivePowerSystemPushforwardCocone (hF : IsReflexive F) :
    Nonempty (Limits.IsColimit (reflexivePowerSystemPushforwardCocone F s)) :=
  ⟨isColimitOfForallIsAffineOpen _ (exists_leg_app_eq_of_isAffineOpen' F s hF)
    fun W _ n η h => exists_map_app_eq_zero_of_cocone_ι_app_eq_zero F s hF
      (genericPoint_mem_sectionIsomorphismOpen (X := X) (F := F) (s := s)) W n η h⟩

end Stacks.AlgebraicGeometry.ReflexivePowers

end
