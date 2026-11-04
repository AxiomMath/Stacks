module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleLength
public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.ArtinReesSeparation
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Coherence
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending sections of an injective quasi-coherent module to the whole scheme

Let `X` be a Noetherian scheme and `𝒥` an injective object of the category of quasi-coherent
`𝒪_X`-modules. This file proves that every section of `𝒥` over an open `U` is the restriction of
a global section, and hence that `𝒥` is a flasque sheaf of `𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.pushforwardRestrict`: the direct image `j_* (ℳ|_U)` of the restriction of a
  sheaf of modules to an open.
* `AlgebraicGeometry.pushforwardRestrictUnit`: the adjunction unit `ℳ ⟶ j_* (ℳ|_U)`.
* `AlgebraicGeometry.vanishingOnOpen`: the subsheaf of sections vanishing on `U`, the kernel of
  that unit.

## Main results

* `AlgebraicGeometry.exists_coherentSubsheaf_of_section`: a section of a quasi-coherent module
  over an open comes from a coherent submodule.
* `AlgebraicGeometry.exists_separatedSubsheaf_of_section`: it comes from a submodule for which
  the unit `ℋ ⟶ j_* (ℋ|_U)` is a monomorphism.
* `AlgebraicGeometry.isFlasque_of_forall_exists_sectionOverTop`: a sheaf of modules all of whose
  sections extend to the whole space is flasque.
* `AlgebraicGeometry.exists_sectionOverTop_of_injective_quasicoherent`: every section of an
  injective quasi-coherent module over an open extends to a global section.
* `AlgebraicGeometry.isFlasque_of_injective_quasicoherent`: an injective quasi-coherent module
  on a Noetherian scheme is flasque.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 09T2](https://stacks.math.columbia.edu/tag/09T2)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace AlgebraicGeometry

section

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Generalities on sheaves of modules on a scheme -/

/-- A morphism of sheaves of modules on a scheme which is injective on sections over every open
is a monomorphism. -/
public lemma Scheme.Modules.mono_of_injective_app {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ V : X.Opens, Function.Injective (f.app V)) : Mono f := by
  refine ⟨fun {Z} g g' hgg' => Scheme.Modules.hom_ext _ _ fun V => ?_⟩
  have hV : g.app V ≫ f.app V = g'.app V ≫ f.app V := by
    rw [← Scheme.Modules.Hom.comp_app, ← Scheme.Modules.Hom.comp_app, hgg']
  ext x
  exact h V (congr($hV x))

/-- A morphism of sheaves of modules on a scheme whose kernel on sections is trivial over every
open is a monomorphism. -/
public lemma Scheme.Modules.mono_of_app_eq_zero {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ (V : X.Opens) (y : Γ(M, V)), (f.val.app (op V)).hom y = 0 → y = 0) : Mono f := by
  refine Scheme.Modules.mono_of_injective_app f fun V y y' hyy' => sub_eq_zero.1 (h V (y - y') ?_)
  have h1 : (f.val.app (op V)).hom y = (f.val.app (op V)).hom y' := hyy'
  refine ((f.val.app (op V)).hom.map_sub y y').trans ?_
  rw [h1, sub_self]

/-- A section of a sheaf of modules whose restriction to an open equal to the one carrying it
vanishes is itself zero. -/
public lemma Scheme.Modules.eq_zero_of_val_map_eq_zero {M : X.Modules} {A B : X.Opens}
    (hle : A ≤ B) (heq : A = B) (y : Γ(M, B)) (hy : M.val.map (homOfLE hle).op y = 0) :
    y = 0 := by
  subst heq
  rwa [Subsingleton.elim (homOfLE hle).op (𝟙 (op A)), M.val.map_id] at hy

/-- A restriction map of a sheaf of modules between two opens which are equal is surjective. -/
public lemma Scheme.Modules.exists_val_map_eq_of_opens_eq {M : X.Modules} {A B : X.Opens}
    (hle : A ≤ B) (heq : A = B) (y : Γ(M, A)) :
    ∃ σ : Γ(M, B), M.val.map (homOfLE hle).op σ = y := by
  subst heq
  refine ⟨y, ?_⟩
  rw [Subsingleton.elim (homOfLE hle).op (𝟙 (op A)), M.val.map_id]
  rfl

/-- Every point of an open lies in an affine open contained in it. -/
private lemma exists_affineOpens_le_of_mem {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ (W : X.Opens) ≤ U := by
  obtain ⟨V', ⟨W, hWaff, hWV'⟩, hxV', hV'U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨⟨W, hWaff⟩, show x ∈ (W : Set X) from hWV' ▸ hxV',
    show (W : Set X) ⊆ U from hWV' ▸ hV'U⟩

/-- A section of a sheaf of modules on a scheme lying in two submodules whose sections meet in
zero over every affine open is zero. -/
public lemma Scheme.Modules.eq_zero_of_mem_inf_of_affineOpens {M : X.Modules}
    (A B : M.Submodule)
    (h : ∀ V : X.affineOpens,
      A.toSubmodule.obj (op V.1) ⊓ B.toSubmodule.obj (op V.1) = ⊥)
    (V : X.Opens) (y : Γ(M, V)) (hA : y ∈ A.toSubmodule.obj (op V))
    (hB : y ∈ B.toSubmodule.obj (op V)) : y = 0 := by
  refine Stacks.Cohomology.InjectiveRestriction.eq_zero_of_locally_zero M y fun x hx => ?_
  obtain ⟨Wa, hxW, hWV⟩ := exists_affineOpens_le_of_mem hx
  refine ⟨Wa.1, hWV, hxW, ?_⟩
  have hmem : M.val.map (homOfLE hWV).op y ∈
      A.toSubmodule.obj (op Wa.1) ⊓ B.toSubmodule.obj (op Wa.1) :=
    ⟨A.toSubmodule.map_mem (homOfLE hWV).op hA, B.toSubmodule.map_mem (homOfLE hWV).op hB⟩
  rw [h Wa] at hmem
  exact (Submodule.mem_bot _).1 hmem

/-- If `ℐ ^ N 𝒮 = 0` for a quasi-coherent submodule `𝒮`, then every element of `ℐ(V) ^ N`
annihilates every section of `𝒮` over an affine open `V`. -/
public lemma Scheme.Modules.smul_eq_zero_of_isZero_idealPowSmul {M : X.Modules}
    (S : M.Submodule) [S.toSheafOfModules.IsQuasicoherent] (I : X.IdealSheafData) (N : ℕ)
    (hz : IsZero (Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul I N
      S.toSheafOfModules).toSheafOfModules)
    (V : X.affineOpens) (a : Γ(X, V.1)) (ha : a ∈ I.ideal V ^ N)
    (m : Γ(M, V.1)) (hm : m ∈ S.toSubmodule.obj (op V.1)) : a • m = 0 := by
  have hbot : I.ideal V ^ N • (⊤ : Submodule Γ(X, V.1) Γ(S.toSheafOfModules, V.1)) = ⊥ := by
    rw [← Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul]
    exact Stacks.Algebraization.submodule_obj_eq_bot_of_isZero _ hz V.1
  have hmem : ∀ y : Γ(S.toSheafOfModules, V.1),
      a • y ∈ I.ideal V ^ N • (⊤ : Submodule Γ(X, V.1) Γ(S.toSheafOfModules, V.1)) :=
    fun _ => Submodule.smul_mem_smul ha Submodule.mem_top
  rw [hbot] at hmem
  have h0 := hmem ⟨m, hm⟩
  rw [Submodule.mem_bot] at h0
  exact congrArg Subtype.val h0

/-! ### The direct image of the restriction to an open -/

/-- The direct image `j_* (ℳ|_U)` of the restriction of a sheaf of modules to an open `U`, for
`j : U → X` the inclusion. Its sections over `V` are the sections of `ℳ` over `V ⊓ U`. -/
public def pushforwardRestrict (U : X.Opens) (M : X.Modules) : X.Modules :=
  (Scheme.Modules.pushforward U.ι).obj (M.restrict U.ι)

/-- The adjunction unit `ℳ ⟶ j_* (ℳ|_U)`. Over an open `V` it is the restriction of sections
from `V` to `V ⊓ U`. -/
public def pushforwardRestrictUnit (U : X.Opens) (M : X.Modules) :
    M ⟶ pushforwardRestrict U M :=
  (Scheme.Modules.restrictAdjunction U.ι).unit.app M

/-- On a Noetherian scheme, the direct image of the restriction of a quasi-coherent module to an
open is quasi-coherent. -/
public instance isQuasicoherent_pushforwardRestrict [IsNoetherian X] (U : X.Opens)
    (M : X.Modules) [M.IsQuasicoherent] : (pushforwardRestrict U M).IsQuasicoherent :=
  AlgebraicGeometry.pushforward_isQuasicoherent U.ι _

/-- The unit `ℳ ⟶ j_* (ℳ|_U)` is, on sections over `V`, the restriction map of `ℳ` to the image
under `j` of the preimage of `V`. -/
public lemma pushforwardRestrictUnit_val_app (U : X.Opens) (M : X.Modules) (V : X.Opens)
    (y : Γ(M, V)) :
    (pushforwardRestrictUnit U M).val.app (op V) y =
      M.val.map (homOfLE (U.ι.image_preimage_le V)).op y :=
  rfl

/-- Over an open contained in `U` the unit `ℳ ⟶ j_* (ℳ|_U)` is injective on sections. -/
public lemma eq_zero_of_pushforwardRestrictUnit_val_app_eq_zero {U : X.Opens} {M : X.Modules}
    {V : X.Opens} (hV : V ≤ U) (y : Γ(M, V))
    (hy : (pushforwardRestrictUnit U M).val.app (op V) y = 0) : y = 0 := by
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hV
  exact Scheme.Modules.eq_zero_of_val_map_eq_zero (M := M) (U.ι.image_preimage_le V) heq y hy

/-- Every section of `j_* (ℳ|_U)` over `U` is the restriction of a section over the whole
scheme. -/
public lemma exists_sectionOverTop_pushforwardRestrict (U : X.Opens) (M : X.Modules)
    (y : Γ(pushforwardRestrict U M, U)) :
    ∃ σ : Γ(pushforwardRestrict U M, ⊤),
      (pushforwardRestrict U M).val.map (homOfLE (le_top : U ≤ ⊤)).op σ = y := by
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ U) = U.ι ''ᵁ (U.ι ⁻¹ᵁ (⊤ : X.Opens)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_top_eq,
      inf_idem]
  exact Scheme.Modules.exists_val_map_eq_of_opens_eq (M := M) (le_of_eq heq) heq
    (show Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ U)) from y)

/-- The subsheaf of sections of `ℳ` vanishing on the open `U`: the kernel of the unit
`ℳ ⟶ j_* (ℳ|_U)`. -/
public def vanishingOnOpen (U : X.Opens) (M : X.Modules) : M.Submodule :=
  Scheme.Modules.kernelSubmodule (pushforwardRestrictUnit U M)

/-- On a Noetherian scheme, the subsheaf of sections of a quasi-coherent module vanishing on an
open is quasi-coherent. -/
public lemma isQuasicoherent_vanishingOnOpen [IsNoetherian X] (U : X.Opens) (M : X.Modules)
    [M.IsQuasicoherent] : (vanishingOnOpen U M).toSheafOfModules.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Scheme.Modules.kernelSubmoduleIso (pushforwardRestrictUnit U M)).symm
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel (pushforwardRestrictUnit U M))

/-- Over an open contained in `U` there are no nonzero sections vanishing on `U`. -/
public lemma obj_vanishingOnOpen_eq_bot (U : X.Opens) (M : X.Modules) {V : X.Opens}
    (hV : V ≤ U) : (vanishingOnOpen U M).toSubmodule.obj (op V) = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun y hy => eq_zero_of_pushforwardRestrictUnit_val_app_eq_zero hV y hy

/-- The subsheaf of sections vanishing on `U` is supported in the complement of `U`. -/
public lemma supp_vanishingOnOpen_subset [IsNoetherian X] (U : X.Opens) (M : X.Modules)
    [M.IsQuasicoherent] :
    SheafOfModules.supp (vanishingOnOpen U M).toSheafOfModules ⊆ ((U : Set X))ᶜ := by
  intro x hx
  by_contra hxU
  rw [Set.notMem_compl_iff] at hxU
  obtain ⟨Wa, hxW, hWU⟩ := exists_affineOpens_le_of_mem (show x ∈ U from hxU)
  refine Stacks.AlgebraicGeometry.IdealPowerSmul.notMem_supp_of_smul_eq_zero M (vanishingOnOpen U M)
    (isQuasicoherent_vanishingOnOpen U M) Wa x hxW 1 ?_ ?_ hx
  · exact fun h => (Wa.2.primeIdealOf ⟨x, hxW⟩).2.ne_top ((Ideal.eq_top_iff_one _).2 h)
  · intro m hm
    rw [show m = 0 from eq_zero_of_pushforwardRestrictUnit_val_app_eq_zero hWU m hm, smul_zero]

/-! ### Cutting a section down to a well-behaved submodule -/

/-- On a Noetherian scheme, a section of a quasi-coherent module over an open comes from a
coherent submodule. -/
public theorem exists_coherentSubsheaf_of_section [IsNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (s : Γ(F, U)) :
    ∃ (G : X.Modules) (_ : G.IsQuasicoherent) (_ : G.IsCoherent) (j : G ⟶ F) (t : Γ(G, U)),
      j.val.app (op U) t = s := by
  have hext : ∀ G : Subobject (F.restrict U.ι),
      (G : U.toScheme.Modules).IsQuasicoherent → (G : U.toScheme.Modules).IsFiniteType →
      ∃ G' : Subobject F, (G' : X.Modules).IsQuasicoherent ∧ (G' : X.Modules).IsFiniteType ∧
        ∃ e : (G' : X.Modules).restrict U.ι ≅ (G : U.toScheme.Modules),
          (Scheme.Modules.restrictFunctor U.ι).map G'.arrow = e.hom ≫ G.arrow := by
    intro G _ _
    exact exists_finiteTypeQuasicoherentSubobject_extension F U (NoetherianSpace.isCompact _) G
  obtain ⟨G, z, hz⟩ := exists_finiteTypeQuasicoherentSubobject_section_of_extension F U s hext
  have hqc : ((G.1 : X.Modules)).IsQuasicoherent := G.2.1
  have hft : ((G.1 : X.Modules)).IsFiniteType := G.2.2
  exact ⟨(G.1 : X.Modules), hqc,
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _,
    G.1.arrow, z, hz⟩

/-- On a Noetherian scheme, a section of a quasi-coherent module over an open `U` comes from a
quasi-coherent submodule `ℋ` for which the adjunction unit `ℋ ⟶ j_* (ℋ|_U)` is a
monomorphism. -/
public theorem exists_separatedSubsheaf_of_section [IsNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (s : Γ(F, U)) :
    ∃ (H : X.Modules) (_ : H.IsQuasicoherent) (j : H ⟶ F) (t : Γ(H, U)),
      Mono (pushforwardRestrictUnit U H) ∧ j.val.app (op U) t = s := by
  obtain ⟨G, hGqc, hGco, jG, t₀, ht₀⟩ := exists_coherentSubsheaf_of_section F U s
  have := hGqc
  have := hGco
  set I : X.IdealSheafData := Scheme.IdealSheafData.complementIdeal U with hIdef
  set T : G.Submodule := vanishingOnOpen U G
  have hTqc : T.toSheafOfModules.IsQuasicoherent := isQuasicoherent_vanishingOnOpen U G
  have hTco : T.toSheafOfModules.IsCoherent :=
    Stacks.AlgebraicGeometry.IdealPowerSmul.isCoherent_of_isQuasicoherent_submodule G T hTqc
  obtain ⟨N, hN⟩ := Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isZero_idealPowSmul
    T.toSheafOfModules ⟨(U : Set X)ᶜ, U.2.isClosed_compl⟩
    (by simpa using supp_vanishingOnOpen_subset U G)
  have hkill : ∀ (V : X.affineOpens) (a : Γ(X, V.1)), a ∈ I.ideal V ^ N →
      ∀ m ∈ (show Submodule Γ(X, V.1) Γ(G, V.1) from T.toSubmodule.obj (op V.1)),
        a • m = 0 :=
    fun V a ha m hm =>
      Scheme.Modules.smul_eq_zero_of_isZero_idealPowSmul T I N hN V a ha m hm
  set Ip : (SheafOfModules.unit X.ringCatSheaf).Submodule :=
    idealPowerMultiple I 1 (SheafOfModules.unit X.ringCatSheaf)
  have hIpqc : Ip.toSheafOfModules.IsQuasicoherent :=
    idealPowerMultiple_unit_isQuasicoherent I 1
  have hIpV : ∀ V : X.affineOpens,
      (show Ideal Γ(X, V.1) from Ip.toSubmodule.obj (op V.1)) = I.ideal V := by
    intro V
    rw [show (show Ideal Γ(X, V.1) from Ip.toSubmodule.obj (op V.1)) = I.ideal V ^ 1 from
      idealPowerMultiple_unit_obj_affineOpens I 1 V, pow_one]
  have hAR : ∀ V : X.affineOpens,
      (show Ideal Γ(X, V.1) from Ip.toSubmodule.obj (op V.1)) ^ N •
          (show Submodule Γ(X, V.1) Γ(G, V.1) from T.toSubmodule.obj (op V.1)) = ⊥ := by
    intro V
    rw [hIpV V]
    refine le_antisymm (Submodule.smul_le.2 fun a ha m hm => ?_) bot_le
    rw [hkill V a ha m hm]
    exact Submodule.zero_mem _
  obtain ⟨m, hm⟩ := exists_idealPow_smul_inf_eq_bot G T Ip N hAR
  have hinf : ∀ V : X.affineOpens,
      (idealPowSmul I m G).toSubmodule.obj (op V.1) ⊓ T.toSubmodule.obj (op V.1) = ⊥ := by
    intro V
    rw [Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul]
    have h1 := hm V
    rwa [hIpV V] at h1
  have hIunit : ∀ W : X.affineOpens, W.1 ≤ U → I.ideal W = ⊤ := fun W hW =>
    ideal_eq_top_of_le_compl_support I W (by rwa [hIdef, coe_support_openComplementIdeal,
      compl_compl])
  have htop : (idealPowSmul I m G).toSubmodule.obj (op U) = ⊤ :=
    Stacks.AlgebraicGeometry.IdealPowerSmul.localSections_idealPowFamily_eq_top I m G hIunit
  refine ⟨(idealPowSmul I m G).toSheafOfModules,
    Stacks.AlgebraicGeometry.IdealPowerSmul.isQuasicoherent_idealPowSmul I m G,
    (idealPowSmul I m G).ι ≫ jG, ⟨t₀, by rw [htop]; exact Submodule.mem_top⟩, ?_, ht₀⟩
  refine Scheme.Modules.mono_of_app_eq_zero _ fun V y hy => ?_
  have hv : (show Γ(G, V) from y.1) ∈ T.toSubmodule.obj (op V) :=
    show (pushforwardRestrictUnit U G).val.app (op V) (show Γ(G, V) from y.1) = 0 from
      congrArg Subtype.val hy
  exact Subtype.ext (Scheme.Modules.eq_zero_of_mem_inf_of_affineOpens (idealPowSmul I m G) T
    hinf V (show Γ(G, V) from y.1) y.2 hv)

/-! ### Flasqueness -/

/-- A sheaf of modules on a scheme whose sections over every open extend to the whole space is
flasque. -/
public theorem isFlasque_of_forall_exists_sectionOverTop (M : X.Modules)
    (H : ∀ (V : X.Opens) (s : Γ(M, V)),
      ∃ t : Γ(M, ⊤), (M.val.map (homOfLE (le_top : V ≤ ⊤)).op).hom t = s) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) where
  epi {V W} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    obtain ⟨t, ht⟩ := H W.unop s
    refine ⟨(M.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom t, ?_⟩
    have hcomp : (homOfLE (le_top : W.unop ≤ ⊤)).op =
        (homOfLE (le_top : V.unop ≤ ⊤)).op ≫ i.unop.op := Subsingleton.elim _ _
    show (M.val.map i.unop.op).hom
      ((M.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom t) = s
    rw [← PresheafOfModules.map_comp_apply M.val
      (homOfLE (le_top : V.unop ≤ ⊤)).op i.unop.op t, ← hcomp, ht]

/-- On a Noetherian scheme, every section over an open of an injective object of the category of
quasi-coherent modules extends to a global section. -/
public theorem exists_sectionOverTop_of_injective_quasicoherent [IsNoetherian X]
    (J : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) [Injective J]
    (U : X.Opens) (s : Γ(J.obj, U)) :
    ∃ t : Γ(J.obj, ⊤), (J.obj.val.map (homOfLE (le_top : U ≤ ⊤)).op).hom t = s := by
  obtain ⟨H, hHqc, j, t, hmono, ht⟩ :=
    exists_separatedSubsheaf_of_section (show X.Modules from J.obj) U s
  have := hHqc
  have hPqc : (pushforwardRestrict U H).IsQuasicoherent := inferInstance
  let A : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := ⟨H, hHqc⟩
  let B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    ⟨pushforwardRestrict U H, hPqc⟩
  let f : A ⟶ B := ObjectProperty.homMk (pushforwardRestrictUnit U H)
  have hmonof : Mono f := (ObjectProperty.ι _).mono_of_mono_map (f := f) hmono
  let g : A ⟶ J := ObjectProperty.homMk j
  let ex := Injective.factorThru g f
  have hfac : f ≫ ex = g := Injective.comp_factorThru g f
  have hfac' : pushforwardRestrictUnit U H ≫ ex.hom = j :=
    congrArg (fun φ : A ⟶ J => InducedCategory.Hom.hom φ) hfac
  obtain ⟨σ, hσ⟩ := exists_sectionOverTop_pushforwardRestrict U H
    ((pushforwardRestrictUnit U H).val.app (op U) t)
  refine ⟨(ex.hom.val.app (op ⊤)).hom σ, ?_⟩
  refine (PresheafOfModules.naturality_apply ex.hom.val
    (homOfLE (le_top : U ≤ ⊤)).op σ).symm.trans ?_
  rw [hσ]
  exact congrArg (fun φ : H ⟶ (show X.Modules from J.obj) => (φ.val.app (op U)).hom t)
    hfac' |>.trans ht

end

/-- Let `X` be a Noetherian scheme and let `𝒥` be an injective
object of the category of quasi-coherent `𝒪_X`-modules. Then `𝒥` is a flasque sheaf of
`𝒪_X`-modules. -/
@[stacks 09T2]
public theorem isFlasque_of_injective_quasicoherent (X : Scheme.{u}) [IsNoetherian X]
    (J : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) [Injective J] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj J.obj) :=
  isFlasque_of_forall_exists_sectionOverTop (show X.Modules from J.obj)
    fun V s => exists_sectionOverTop_of_injective_quasicoherent J V s

end AlgebraicGeometry

end

end
