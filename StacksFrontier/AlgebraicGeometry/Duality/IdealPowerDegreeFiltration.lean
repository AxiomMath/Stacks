module

public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerSubmoduleArtinRees
import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple

/-!
# The ideal-power filtration of a complex in one degree

Fix a complex `𝓕^•` of modules on a scheme `X`, a quasi-coherent sheaf of ideals `𝓘` and a degree
`p`, and work inside the single module `L = 𝓕^p`. The cycles `Z = ker(d^p)` and the boundaries
`B = im(d^{p-1})` are submodules of `L`, as are the ideal-power multiple `P n = 𝓘^n L`, the image
`C n = d^{p-1}(𝓘^n 𝓕^{p-1})` and the ideal-power multiple `G m = 𝓘^m Z` of the cycles. These are
the subobjects out of which the homology of `𝓕^•` and of `𝓘^n 𝓕^•` in degree `p` are cut, and this
file establishes the containments between them, together with the two forms of Artin-Rees that the
comparison of those homologies needs:

`Z ⊓ P n ≤ G (n - c)` and `B ⊓ P n ≤ C (n - c)`,

for one constant `c`, which is the sheaf-theoretic replacement for the two applications of
Artin-Rees in the algebraic statement.

## Main definitions

* `Stacks.Duality.cycSub`, `bdrySub`, `pwSub`, `bdryPwSub`, `cycPwSub` — the five submodules of
  `𝓕^p` above.

## Main results

* `Stacks.Duality.idealPowerSub_bdrySub` — `𝓘^m B = C m`, which is what turns Artin-Rees for `B`
  into the second containment.
* `Stacks.Duality.exists_artinRees_degree` — both containments, with a single `c > 0`.
* `Stacks.Duality.imageSubmodule_subι_kernelSubmodule_comp` — the image under a monomorphism of a
  sectionwise kernel upstairs is the image of the monomorphism met with the kernel downstairs.

## References

* [Stacks Project, Tag 0G4R](https://stacks.math.columbia.edu/tag/0G4R)
* [Stacks Project, Tag 0G3K](https://stacks.math.columbia.edu/tag/0G3K)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {X : Scheme.{u}}

attribute [local instance] AlgebraicGeometry.sectionsModuleΓSheaf

/-! ### The two presentations of the ideal-power multiple agree -/

/-- The two constructions of the ideal-power multiple `𝓘 ^ n M`,
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` and
`Stacks.Algebraization.idealPowerMultiple`, are the same subsheaf: both are the least one
containing `𝓘(U) ^ n M(U)` on every affine open. -/
lemma idealPowerMultiple_eq_algebraization (I : X.IdealSheafData) (n : ℕ) (M : X.Modules) :
    Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple I n M =
      Stacks.Algebraization.idealPowerMultiple I n M :=
  le_antisymm
    ((Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_le_iff I n M _).2
      fun U => (Stacks.Algebraization.idealPowerMultiple_le_iff I n M _).1 le_rfl U)
    ((Stacks.Algebraization.idealPowerMultiple_le_iff I n M _).2
      fun U =>
        (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_le_iff I n M _).1 le_rfl U)

/-! ### Generic complements on sections -/

/-- Over an affine open the image of `𝓘 ^ n M` under `j` has sections `𝓘(U) ^ n j(M(U))`. Unlike
`AlgebraicGeometry.secs_imageSubmodule_idealPowerMultiple_comp` this needs no monomorphism
hypothesis on `j`, at the cost of quasi-coherence of the target. -/
lemma secs_imageSubmodule_idealPowerMultiple_comp_qc (I : X.IdealSheafData) (n : ℕ)
    {M L : X.Modules} (j : M ⟶ L) (hM : M.IsQuasicoherent) (hL : L.IsQuasicoherent)
    (U : X.affineOpens) :
    secs (imageSubmodule (subι (Stacks.Algebraization.idealPowerMultiple I n M) ≫ j)) U.1 =
      I.ideal U ^ n • LinearMap.range (secMap j U.1) :=
  have hqc : ((Stacks.Algebraization.idealPowerMultiple I n M).toSheafOfModules :
      X.Modules).IsQuasicoherent :=
    Stacks.Algebraization.idealPowerMultiple_isQuasicoherent I n M
  have h1 : secs (imageSubmodule (subι (Stacks.Algebraization.idealPowerMultiple I n M) ≫ j))
        U.1 =
      LinearMap.range (secMap (subι (Stacks.Algebraization.idealPowerMultiple I n M) ≫ j) U.1) :=
    imageSubmodule_obj_affine _ hqc hL U
  h1.trans
    (((congrArg (fun t => LinearMap.range t)
          (secMap_comp (subι (Stacks.Algebraization.idealPowerMultiple I n M)) j U.1)).trans
        (LinearMap.range_comp _ _)).trans
      ((congrArg (Submodule.map (secMap j U.1))
          ((secs_eq_range (Stacks.Algebraization.idealPowerMultiple I n M) U.1).symm.trans
            (secs_idealPowerMultiple I n M hM U))).trans
        ((Submodule.map_smul'' _ _ _).trans
          (congrArg (fun t : Submodule Γ(X, U.1) Γ(L, U.1) => I.ideal U ^ n • t)
            (Submodule.map_top _)))))

/-- The sectionwise kernel of a morphism of quasi-coherent modules is quasi-coherent. -/
lemma isQuasicoherent_kernelSubmodule {M N : X.Modules} (g : M ⟶ N) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) :
    ((Stacks.Algebraization.kernelSubmodule g).toSheafOfModules : X.Modules).IsQuasicoherent :=
  have := hM
  have := hN
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Stacks.Algebraization.kernelSubmoduleIso g).symm
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel g)

/-- The forward map of an isomorphism is invertible. -/
lemma isIso_hom_of_iso {M N : X.Modules} (e : M ≅ N) : IsIso e.hom :=
  inferInstance

/-- An isomorphism is injective on sections. -/
lemma injective_secMap_of_isIso {M N : X.Modules} (f : M ⟶ N) (hf : IsIso f) (U : X.Opens) :
    Function.Injective (secMap f U) :=
  have := hf
  fun a b hab =>
    have h1 : secMap (f ≫ inv f) U a = secMap (f ≫ inv f) U b :=
      congrArg (secMap (inv f) U) hab
    (congrArg (fun k : M ⟶ M => secMap k U a) (IsIso.hom_inv_id f)).symm.trans
      (h1.trans (congrArg (fun k : M ⟶ M => secMap k U b) (IsIso.hom_inv_id f)))

/-- The image under a monomorphism `j` of the sectionwise kernel of a morphism out of its source is
the image of `j` met with the sectionwise kernel downstairs, when `j` carries the one morphism to
the other along a map injective on sections. -/
lemma imageSubmodule_subι_kernelSubmodule_comp {A L C₁ C₂ : X.Modules} (j : A ⟶ L) (hj : Mono j)
    (g : A ⟶ C₁) (k : L ⟶ C₂) (jm : C₁ ⟶ C₂)
    (hjm : ∀ U : X.Opens, Function.Injective (secMap jm U))
    (hsq : j ≫ k = g ≫ jm) :
    imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule g) ≫ j) =
      imageSubmodule j ⊓ Stacks.Algebraization.kernelSubmodule k := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun W => ?_)
  obtain ⟨W, rfl⟩ : ∃ W₀ : X.Opens, op W₀ = W := ⟨W.unop, rfl⟩
  have hsqW : ∀ x : Γ(A, W), secMap k W (secMap j W x) = secMap jm W (secMap g W x) :=
    fun x => congrArg (fun t : A ⟶ C₂ => secMap t W x) hsq
  have hL : secs (imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule g) ≫ j)) W =
      LinearMap.range (secMap (subι (Stacks.Algebraization.kernelSubmodule g) ≫ j) W) :=
    imageSubmodule_subι_comp_obj j hj _ W
  have hR : secs (imageSubmodule j) W = LinearMap.range (secMap j W) :=
    imageSubmodule_obj j hj W
  have hgoal : secs (imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule g) ≫ j)) W =
      secs (imageSubmodule j ⊓ Stacks.Algebraization.kernelSubmodule k) W := by
    rw [hL, secs_inf, hR]
    refine le_antisymm (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨t, rfl⟩ := hs
      have ht : secMap g W t.1 = 0 :=
        (mem_kernelSubmodule_iff g W t.1).1 t.2
      refine ⟨⟨t.1, rfl⟩, ?_⟩
      refine (mem_kernelSubmodule_iff k W _).2 ?_
      have h2 : secMap k W (secMap j W t.1) = 0 := by
        rw [hsqW t.1, ht, map_zero]
      exact h2
    · obtain ⟨⟨x, hx⟩, hsk⟩ := hs
      have hks : secMap k W s = 0 := (mem_kernelSubmodule_iff k W s).1 hsk
      have hgx : secMap g W x = 0 := by
        refine hjm W ?_
        rw [map_zero, ← hsqW x, hx]
        exact hks
      exact ⟨⟨x, (mem_kernelSubmodule_iff g W x).2 hgx⟩, hx⟩
  exact hgoal

/-! ### The five submodules of `𝓕^p` -/

variable (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (p : ℤ)

/-- The cycles of `𝓕^•` in degree `p`, as a submodule of `𝓕^p`. -/
def cycSub : ((F.sc p).X₂).Submodule :=
  Stacks.Algebraization.kernelSubmodule (F.sc p).g

/-- The boundaries of `𝓕^•` in degree `p`, as a submodule of `𝓕^p`. -/
def bdrySub : ((F.sc p).X₂).Submodule :=
  imageSubmodule (F.sc p).f

/-- The submodule `𝓘 ^ n 𝓕^p` of `𝓕^p`. -/
def pwSub (n : ℕ) : ((F.sc p).X₂).Submodule :=
  Stacks.Algebraization.idealPowerMultiple I n ((F.sc p).X₂)

/-- The image of `𝓘 ^ n 𝓕^{p-1}` under the differential, as a submodule of `𝓕^p`. -/
def bdryPwSub (n : ℕ) : ((F.sc p).X₂).Submodule :=
  imageSubmodule (subι (Stacks.Algebraization.idealPowerMultiple I n ((F.sc p).X₁)) ≫ (F.sc p).f)

/-- The submodule `𝓘 ^ m Z` of `𝓕^p`, for `Z` the cycles. -/
def cycPwSub (m : ℕ) : ((F.sc p).X₂).Submodule :=
  idealPowerSub I m (cycSub F p)

/-! ### Containments -/

/-- The boundaries are cycles. -/
lemma bdrySub_le_cycSub : bdrySub F p ≤ cycSub F p :=
  imageSubmodule_le_kernelSubmodule _ _ (F.sc p).zero

/-- The image `C n` of `𝓘 ^ n 𝓕^{p-1}` consists of boundaries. -/
lemma bdryPwSub_le_bdrySub (n : ℕ) : bdryPwSub I F p n ≤ bdrySub F p :=
  imageSubmodule_comp_le _ _

/-- The submodule `𝓘 ^ m Z` is contained in the cycles `Z`. -/
lemma cycPwSub_le_cycSub (m : ℕ) : cycPwSub I F p m ≤ cycSub F p :=
  idealPowerSub_le _ _ _

/-- The images `C n` decrease as `n` grows. -/
lemma bdryPwSub_antitone {m n : ℕ} (h : m ≤ n) : bdryPwSub I F p n ≤ bdryPwSub I F p m :=
  imageSubmodule_subι_comp_mono (F.sc p).f (idealPowerMultiple_antitone I _ h)

/-- The submodules `𝓘 ^ m Z` decrease as `m` grows. -/
lemma cycPwSub_antitone {m n : ℕ} (h : m ≤ n) : cycPwSub I F p n ≤ cycPwSub I F p m :=
  idealPowerSub_antitone I _ h

/-- The submodules `𝓘 ^ n 𝓕^p` decrease as `n` grows. -/
lemma pwSub_antitone {m n : ℕ} (h : m ≤ n) : pwSub I F p n ≤ pwSub I F p m :=
  idealPowerMultiple_antitone I _ h

/-- Every term of the complex is a coherent module. -/
abbrev TermsCoherent (F : CochainComplex X.Modules ℤ) : Prop :=
  ∀ i : ℤ, _root_.SheafOfModules.IsCoherent (F.X i)

/-- The terms of a complex of coherent modules are quasi-coherent. -/
lemma isQuasicoherent_X (hF : TermsCoherent F) (i : ℤ) : (F.X i).IsQuasicoherent :=
  have := hF i
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent (F.X i)).1

/-- The cycles of a complex of coherent modules are quasi-coherent. -/
lemma isQuasicoherent_cycSub (hF : TermsCoherent F) :
    ((cycSub F p).toSheafOfModules : X.Modules).IsQuasicoherent :=
  isQuasicoherent_kernelSubmodule (F.sc p).g (isQuasicoherent_X F hF p)
    (isQuasicoherent_X F hF ((ComplexShape.up ℤ).next p))

/-- The boundaries of a complex of coherent modules are quasi-coherent. -/
lemma isQuasicoherent_bdrySub (hF : TermsCoherent F) :
    ((bdrySub F p).toSheafOfModules : X.Modules).IsQuasicoherent :=
  have _h1 : ((F.sc p).X₁).IsQuasicoherent :=
    isQuasicoherent_X F hF ((ComplexShape.up ℤ).prev p)
  have _h2 : ((F.sc p).X₂).IsQuasicoherent := isQuasicoherent_X F hF p
  isQuasicoherent_imageSubmodule (F.sc p).f

/-- The image `C n` of `𝓘 ^ n 𝓕^{p-1}` is quasi-coherent for a complex of coherent modules. -/
lemma isQuasicoherent_bdryPwSub (hF : TermsCoherent F) (n : ℕ) :
    ((bdryPwSub I F p n).toSheafOfModules : X.Modules).IsQuasicoherent :=
  have _h1 : ((F.sc p).X₁).IsQuasicoherent :=
    isQuasicoherent_X F hF ((ComplexShape.up ℤ).prev p)
  have _h2 : ((F.sc p).X₂).IsQuasicoherent := isQuasicoherent_X F hF p
  have _h3 : ((Stacks.Algebraization.idealPowerMultiple I n ((F.sc p).X₁)).toSheafOfModules :
      X.Modules).IsQuasicoherent :=
    Stacks.Algebraization.idealPowerMultiple_isQuasicoherent I n _
  isQuasicoherent_imageSubmodule _

/-- The submodule `𝓘 ^ m Z` is quasi-coherent for a complex of coherent modules. -/
lemma isQuasicoherent_cycPwSub (hF : TermsCoherent F) (m : ℕ) :
    ((cycPwSub I F p m).toSheafOfModules : X.Modules).IsQuasicoherent :=
  have _h2 : ((F.sc p).X₂).IsQuasicoherent := isQuasicoherent_X F hF p
  have _h4 := isQuasicoherent_cycSub F p hF
  have _h3 : ((Stacks.Algebraization.idealPowerMultiple I m
      ((cycSub F p).toSheafOfModules : X.Modules)).toSheafOfModules :
        X.Modules).IsQuasicoherent :=
    Stacks.Algebraization.idealPowerMultiple_isQuasicoherent I m _
  isQuasicoherent_imageSubmodule _

/-- The sections of the boundaries over an affine open are the image of the sections of the
differential. -/
lemma secs_bdrySub (hF : TermsCoherent F) (U : X.affineOpens) :
    secs (bdrySub F p) U.1 = LinearMap.range (secMap (F.sc p).f U.1) :=
  imageSubmodule_obj_affine (F.sc p).f
    (isQuasicoherent_X F hF ((ComplexShape.up ℤ).prev p)) (isQuasicoherent_X F hF p) U

/-- The sections of `C n` over an affine open are `𝓘(U) ^ n` times the image of the sections of the
differential. -/
lemma secs_bdryPwSub (hF : TermsCoherent F) (n : ℕ) (U : X.affineOpens) :
    secs (bdryPwSub I F p n) U.1 = I.ideal U ^ n • LinearMap.range (secMap (F.sc p).f U.1) :=
  secs_imageSubmodule_idealPowerMultiple_comp_qc I n (F.sc p).f
    (isQuasicoherent_X F hF ((ComplexShape.up ℤ).prev p)) (isQuasicoherent_X F hF p) U

/-- **`𝓘 ^ m B = C m`**: the ideal-power multiple of the boundaries is the image of the ideal-power
multiple of the previous term. -/
lemma idealPowerSub_bdrySub (hF : TermsCoherent F) (m : ℕ) :
    idealPowerSub I m (bdrySub F p) = bdryPwSub I F p m := by
  have key : ∀ U : X.affineOpens,
      secs (idealPowerSub I m (bdrySub F p)) U.1 = secs (bdryPwSub I F p m) U.1 := fun U => by
    rw [idealPowerSub_obj_affine I m (bdrySub F p) (isQuasicoherent_bdrySub F p hF) U,
      secs_bdrySub F p hF U, secs_bdryPwSub I F p hF m U]
  exact le_antisymm (Stacks.Algebraization.submodule_le_of_affine _ _ fun U => (key U).le)
    (Stacks.Algebraization.submodule_le_of_affine _ _ fun U => (key U).ge)

/-- Sections of `𝓘 ^ n 𝓕^p` over an affine open contain `𝓘(U) ^ n` times any sections. -/
private lemma smul_le_secs_pwSub (n : ℕ) (U : X.affineOpens)
    (S : Submodule Γ(X, U.1) Γ((F.sc p).X₂, U.1)) :
    I.ideal U ^ n • S ≤ secs (pwSub I F p n) U.1 :=
  (Submodule.smul_mono le_rfl le_top).trans
    ((Stacks.Algebraization.idealPowerMultiple_le_iff I n ((F.sc p).X₂) _).1 le_rfl U)

/-- The image `C n` of `𝓘 ^ n 𝓕^{p-1}` is contained in `𝓘 ^ n 𝓕^p`. -/
lemma bdryPwSub_le_pwSub (hF : TermsCoherent F) (n : ℕ) :
    bdryPwSub I F p n ≤ pwSub I F p n :=
  Stacks.Algebraization.submodule_le_of_affine _ _ fun U =>
    (secs_bdryPwSub I F p hF n U).le.trans (smul_le_secs_pwSub I F p n U _)

/-- The submodule `𝓘 ^ m Z` is contained in `𝓘 ^ m 𝓕^p`. -/
lemma cycPwSub_le_pwSub (hF : TermsCoherent F) (m : ℕ) :
    cycPwSub I F p m ≤ pwSub I F p m :=
  Stacks.Algebraization.submodule_le_of_affine _ _ fun U =>
    (idealPowerSub_obj_affine I m (cycSub F p) (isQuasicoherent_cycSub F p hF) U).le.trans
      (smul_le_secs_pwSub I F p m U _)

/-! ### Artin-Rees in degree `p` -/

/-- **The two Artin-Rees containments in degree `p`, with one constant.** This is the sheaf-level
replacement for the two applications of Artin-Rees in the algebraic statement, and `c = c₁ + c₂` is
formed exactly as there. -/
lemma exists_artinRees_degree [IsNoetherian X] (hF : TermsCoherent F) :
    ∃ c : ℕ, 0 < c ∧
      (∀ n : ℕ, c ≤ n → cycSub F p ⊓ pwSub I F p n ≤ cycPwSub I F p (n - c)) ∧
      (∀ n : ℕ, c ≤ n → bdrySub F p ⊓ pwSub I F p n ≤ bdryPwSub I F p (n - c)) := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := exists_idealPowerSub_artinRees I ((F.sc p).X₂) (hF p)
    (bdrySub F p) (isQuasicoherent_bdrySub F p hF)
  obtain ⟨c₂, hc₂pos, hc₂⟩ := exists_idealPowerSub_artinRees I ((F.sc p).X₂) (hF p)
    (cycSub F p) (isQuasicoherent_cycSub F p hF)
  refine ⟨c₁ + c₂, by omega, fun n hn => ?_, fun n hn => ?_⟩
  · exact (inf_comm _ _).le.trans ((hc₂ n (by omega)).trans (cycPwSub_antitone I F p (by omega)))
  · refine (inf_comm _ _).le.trans ((hc₁ n (by omega)).trans ?_)
    rw [idealPowerSub_bdrySub I F p hF]
    exact bdryPwSub_antitone I F p (by omega)

/-! ### Transport along an equality of submodules -/

/-- Equal submodules have equal underlying modules. -/
def submoduleEqIso {L : X.Modules} {Q Q' : L.Submodule} (h : Q = Q') :
    ((Q.toSheafOfModules : X.Modules)) ≅ ((Q'.toSheafOfModules : X.Modules)) :=
  eqToIso (congrArg (fun K : L.Submodule => (K.toSheafOfModules : X.Modules)) h)

/-- The identification of equal submodules commutes with their inclusions. -/
lemma submoduleEqIso_hom_comp_subι {L : X.Modules} {Q Q' : L.Submodule} (h : Q = Q') :
    (submoduleEqIso h).hom ≫ subι Q' = subι Q := by
  cases h
  exact Category.id_comp _

/-! ### The homology in degree `p`, and its ideal-power multiples -/

/-- The homology of `𝓕^•` in degree `p`, as the subquotient `Z / B` of `𝓕^p`. -/
abbrev homSub : X.Modules := subq (bdrySub F p) (cycSub F p) (bdrySub_le_cycSub F p)

/-- The projection of the cycles onto the homology. -/
abbrev homSubπ : ((cycSub F p).toSheafOfModules : X.Modules) ⟶ homSub F p :=
  subqπ (bdrySub F p) (cycSub F p) (bdrySub_le_cycSub F p)

/-- The canonical map `(𝓘^m Z) / (𝓘^m Z ⊓ B) ⟶ 𝓗`. -/
def homSubPwMap (m : ℕ) :
    subq (cycPwSub I F p m ⊓ bdrySub F p) (cycPwSub I F p m) inf_le_left ⟶ homSub F p :=
  subqMap inf_le_left (bdrySub_le_cycSub F p) (cycPwSub_le_cycSub I F p m) inf_le_right

/-- The homology in degree `p` of a complex of coherent modules is quasi-coherent. -/
lemma isQuasicoherent_homSub (hF : TermsCoherent F) : (homSub F p).IsQuasicoherent :=
  have _h2 : ((F.sc p).X₂).IsQuasicoherent := isQuasicoherent_X F hF p
  have _h4 := isQuasicoherent_cycSub F p hF
  have _h5 := isQuasicoherent_bdrySub F p hF
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
    (subHom (bdrySub_le_cycSub F p))

/-- The submodule `𝓘 ^ m Z ⊓ B` is quasi-coherent for a complex of coherent modules. -/
lemma isQuasicoherent_cycPwSub_inf_bdrySub (hF : TermsCoherent F) (m : ℕ) :
    ((cycPwSub I F p m ⊓ bdrySub F p).toSheafOfModules : X.Modules).IsQuasicoherent :=
  have _h1 : ((F.sc p).X₁).IsQuasicoherent :=
    isQuasicoherent_X F hF ((ComplexShape.up ℤ).prev p)
  have _h2 : ((F.sc p).X₂).IsQuasicoherent := isQuasicoherent_X F hF p
  isQuasicoherent_inf_kernelSubmodule (cycPwSub I F p m) (isQuasicoherent_cycPwSub I F p hF m)
    (cokernel.π (C := X.Modules) (F.sc p).f)

/-- The inclusion of `𝓘^m Z` into `Z`, read through the identification of `𝓘^m Z` with the
ideal-power multiple of the module of cycles. -/
lemma imageSubmoduleIso_hom_comp_subHom (m : ℕ) :
    (imageSubmoduleIso (subι (Stacks.Algebraization.idealPowerMultiple I m
        ((cycSub F p).toSheafOfModules : X.Modules)) ≫ subι (cycSub F p))
      (mono_subι_comp (subι (cycSub F p)) (mono_subι _) _)).hom ≫
        subHom (cycPwSub_le_cycSub I F p m) =
      subι (Stacks.Algebraization.idealPowerMultiple I m
        ((cycSub F p).toSheafOfModules : X.Modules)) :=
  cancel_subι (cycSub F p) _ _
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => (imageSubmoduleIso (subι (Stacks.Algebraization.idealPowerMultiple I m
            ((cycSub F p).toSheafOfModules : X.Modules)) ≫ subι (cycSub F p))
          (mono_subι_comp (subι (cycSub F p)) (mono_subι _) _)).hom ≫ t)
        (homOfLE_comp_subι (cycPwSub_le_cycSub I F p m))).trans
        (imageSubmoduleIso_hom_comp_subι _ _)))

/-- **The image of `(𝓘^m Z)/(𝓘^m Z ⊓ B)` in `𝓗` is `𝓘^m 𝓗`.** -/
lemma imageSubmodule_homSubPwMap (hF : TermsCoherent F) (m : ℕ) :
    imageSubmodule (homSubPwMap I F p m) =
      Stacks.Algebraization.idealPowerMultiple I m (homSub F p) := by
  have hkey := imageSubmodule_idealPowerMultiple_of_epi I m (isQuasicoherent_cycSub F p hF)
    (isQuasicoherent_homSub F p hF) (homSubπ F p) (epi_subqπ _ _ _)
  have he : Epi (imageSubmoduleIso (subι (Stacks.Algebraization.idealPowerMultiple I m
      ((cycSub F p).toSheafOfModules : X.Modules)) ≫ subι (cycSub F p))
        (mono_subι_comp (subι (cycSub F p)) (mono_subι _) _)).hom :=
    epi_of_isIso_modules _ (isIso_hom_of_iso _)
  have he2 : Epi (subqπ (cycPwSub I F p m ⊓ bdrySub F p) (cycPwSub I F p m) inf_le_left) :=
    epi_subqπ _ _ _
  have h1 : imageSubmodule (subι (Stacks.Algebraization.idealPowerMultiple I m
        ((cycSub F p).toSheafOfModules : X.Modules)) ≫ homSubπ F p) =
      imageSubmodule (subHom (cycPwSub_le_cycSub I F p m) ≫ homSubπ F p) :=
    (congrArg (fun t => imageSubmodule (t ≫ homSubπ F p))
        (imageSubmoduleIso_hom_comp_subHom I F p m)).symm.trans
      ((congrArg imageSubmodule (Category.assoc _ _ _)).trans
        (@imageSubmodule_epi_comp X _ _ _ _ he _))
  have h2 : imageSubmodule (homSubPwMap I F p m) =
      imageSubmodule (subHom (cycPwSub_le_cycSub I F p m) ≫ homSubπ F p) :=
    (@imageSubmodule_epi_comp X _ _ _ _ he2 (homSubPwMap I F p m)).symm.trans
      (congrArg imageSubmodule (subqπ_comp_subqMap _ _ _ _))
  rw [h2, ← h1, hkey]

/-- The canonical map `(𝓘^m Z) / (𝓘^m Z ⊓ B) ⟶ 𝓗` is a monomorphism. -/
lemma mono_homSubPwMap (hF : TermsCoherent F) (m : ℕ) : Mono (homSubPwMap I F p m) :=
  mono_subqMap inf_le_left (bdrySub_le_cycSub F p) (cycPwSub_le_cycSub I F p m) inf_le_right
    (isQuasicoherent_cycPwSub I F p hF m)
    (isQuasicoherent_cycPwSub_inf_bdrySub I F p hF m) le_rfl

/-- **`𝓘 ^ m 𝓗` is the subquotient `(𝓘^m Z) / (𝓘^m Z ⊓ B)` of `𝓕^p`.** -/
def idealPowerHomIso (hF : TermsCoherent F) (m : ℕ) :
    subq (cycPwSub I F p m ⊓ bdrySub F p) (cycPwSub I F p m) inf_le_left ≅
      ((Stacks.Algebraization.idealPowerMultiple I m (homSub F p)).toSheafOfModules :
        X.Modules) :=
  imageSubmoduleIso (homSubPwMap I F p m) (mono_homSubPwMap I F p hF m) ≪≫
    submoduleEqIso (imageSubmodule_homSubPwMap I F p hF m)

/-- The identification of `(𝓘^m Z) / (𝓘^m Z ⊓ B)` with `𝓘 ^ m 𝓗`, followed by the inclusion
into `𝓗`, is the canonical map. -/
lemma idealPowerHomIso_hom_comp_subι (hF : TermsCoherent F) (m : ℕ) :
    (idealPowerHomIso I F p hF m).hom ≫
        subι (Stacks.Algebraization.idealPowerMultiple I m (homSub F p)) =
      homSubPwMap I F p m :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (imageSubmoduleIso (homSubPwMap I F p m)
        (mono_homSubPwMap I F p hF m)).hom ≫ t)
      (submoduleEqIso_hom_comp_subι (imageSubmodule_homSubPwMap I F p hF m))).trans
      (imageSubmoduleIso_hom_comp_subι _ _))

end Stacks.Duality

end
