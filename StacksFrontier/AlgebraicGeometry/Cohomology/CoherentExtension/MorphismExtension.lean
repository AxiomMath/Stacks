module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerAnnihilation
public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.ArtinReesSeparation
public import StacksFrontier.AlgebraicGeometry.IntegralReduction.Transport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Support
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.GraphKernel
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeGeneration
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension

/-!
# Extending a morphism of coherent modules off an open subscheme

Let `X` be a Noetherian scheme, `F` a coherent and `G` a quasi-coherent `𝒪_X`-module, and
`U ⊆ X` an open subscheme. A morphism `φ : F|_U ⟶ G|_U` need not extend to `X`, but it does
after replacing `F` by a coherent submodule agreeing with it on `U`: there are a coherent `F'`,
a monomorphism `F' ⟶ F` which is an isomorphism over `U`, and a morphism `F' ⟶ G` restricting
to `φ`.

The construction extends the *graph* of `φ` rather than `φ` itself. Inside `H = F ⊞ G` the
graph of `φ` is the image of `F|_U ⟶ H|_U`, `x ↦ (x, φ x)`, a finite-type quasi-coherent
subobject of `H|_U`; extending it over the quasi-compact `X` produces a finite-type
quasi-coherent `K ⊆ H` agreeing with the graph over `U`. The composite `K ⟶ H ⟶ F` is then an
isomorphism over `U`, so its sectionwise kernel `L` vanishes on `U` and hence is supported in
the closed complement of `U`. Taking `ℐ` for the ideal sheaf of that closed set, a power of
`ℐ` annihilates `L`, and Artin–Rees separates `L` from a high enough power:
`ℐ ^ m K ⊓ L = 0`. So `ℐ ^ m K` maps monomorphically to `F`, and it still agrees with `F` over
`U` because `ℐ` is the unit ideal there.

## Main results

* `AlgebraicGeometry.exists_coherent_submodule_of_isIso_restrict` — the separation argument:
  a morphism of coherent modules which is invertible over `U` becomes a monomorphism after
  restricting its source to an ideal power, without disturbing it over `U`.
* `AlgebraicGeometry.exists_coherent_submodule_extension_of_isNoetherian` — the extension
  statement above, on a Noetherian scheme.

## Implementation notes

The extension step is `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension`,
which needs the ambient scheme to be quasi-compact and quasi-separated; both hold for a
Noetherian scheme, the second because a Noetherian topological space has every subset compact.
The annihilation step is
`AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset` and the separation step is
`AlgebraicGeometry.exists_idealPow_smul_inf_eq_bot`, which packages Artin–Rees in exactly the
form used here.

The subsheaf `ℐ ^ m K` is `Stacks.AlgebraicGeometry.IdealPowerSmul.idealPowSmul`, the
construction of this subsheaf whose sections over an *arbitrary* open are available: over an
affine open they are `ℐ(V) ^ m Γ(K, V)`, which is what the separation step compares against,
and over an open contained in `U` they are everything, which is what the agreement with `F`
over `U` needs.

The kernel of `K ⟶ F` is taken sectionwise, as `Stacks.Algebraization.kernelSubmodule`, so
that its sections over an open are literally the kernel on sections; it is isomorphic to the
categorical kernel, which is where its quasi-coherence comes from.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 0FD0](https://stacks.math.columbia.edu/tag/0FD0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Algebraization (kernelSubmodule kernelSubmodule_toSubmodule_obj
  kernelSubmodule_obj_affine kernelSubmoduleIso idealKernel_isQuasicoherent
  mem_submodule_of_affine)
open Stacks.AlgebraicGeometry.IdealPowerSmul
open Stacks.AlgebraicGeometry.Tag01YEIntegralReduction (isIso_restrictFunctor_map_of_forall_app
  isIso_app_of_isIso_restrictFunctor_map)

universe u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Monomorphisms detected on sections -/

/-- A morphism of modules on a scheme which is injective on sections over every open is a
monomorphism. -/
lemma mono_of_val_app_injective {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ W : (Opens X)ᵒᵖ, Function.Injective (f.val.app W)) : Mono f :=
  (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
    (PresheafOfModules.mono_of_injective (f := f.val) fun {W} => h W)

/-! ### The graph of a morphism over an open subscheme -/

/-- The graph `x ↦ (x, φ x)` of a morphism `φ : F|_U ⟶ G|_U`, as a morphism into the
restriction of `F ⊞ G`. -/
noncomputable def graphHom (F G : X.Modules) (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    (Scheme.Modules.restrictFunctor U.ι).obj F ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj (F ⊞ G) :=
  (Scheme.Modules.restrictFunctor U.ι).map biprod.inl +
    φ ≫ (Scheme.Modules.restrictFunctor U.ι).map biprod.inr

/-- The graph of `φ` followed by the first projection is the identity. -/
lemma graphHom_comp_fst (F G : X.Modules) (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    graphHom F G U φ ≫ (Scheme.Modules.restrictFunctor U.ι).map biprod.fst = 𝟙 _ := by
  simp [graphHom, Preadditive.add_comp, Category.assoc, ← Functor.map_comp]

/-- The graph of `φ` followed by the second projection is `φ`. -/
lemma graphHom_comp_snd (F G : X.Modules) (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    graphHom F G U φ ≫ (Scheme.Modules.restrictFunctor U.ι).map biprod.snd = φ := by
  simp [graphHom, Preadditive.add_comp, Category.assoc, ← Functor.map_comp]

/-- The graph of `φ` is a monomorphism, being split by the first projection. -/
instance mono_graphHom (F G : X.Modules) (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) : Mono (graphHom F G U φ) :=
  mono_of_mono_fac (graphHom_comp_fst F G U φ)

/-- The first projection restricted to the graph of `φ` is an isomorphism. -/
lemma isIso_graphSubobject_arrow_comp_fst (F G : X.Modules) (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    IsIso ((Subobject.mk (graphHom F G U φ)).arrow ≫
      (Scheme.Modules.restrictFunctor U.ι).map biprod.fst) := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk (graphHom F G U φ)]
  simp only [Category.assoc, graphHom_comp_fst, Category.comp_id]
  infer_instance

/-- The second projection restricted to the graph of `φ` is the first one followed by `φ`. -/
lemma graphSubobject_arrow_comp_snd (F G : X.Modules) (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    (Subobject.mk (graphHom F G U φ)).arrow ≫
        (Scheme.Modules.restrictFunctor U.ι).map biprod.fst ≫ φ =
      (Subobject.mk (graphHom F G U φ)).arrow ≫
        (Scheme.Modules.restrictFunctor U.ι).map biprod.snd := by
  have h1 : graphHom F G U φ ≫
      (Scheme.Modules.restrictFunctor U.ι).map biprod.fst ≫ φ = φ := by
    rw [← Category.assoc, graphHom_comp_fst, Category.id_comp]
  rw [← Subobject.underlyingIso_hom_comp_eq_mk (graphHom F G U φ)]
  simp only [Category.assoc]
  rw [h1, graphHom_comp_snd]

/-! ### Ideal sheaves vanishing on an open -/

/-- An ideal sheaf whose support misses an affine open is the unit ideal there. -/
private lemma ideal_eq_top_of_notMem_support (J : X.IdealSheafData) (W : X.affineOpens)
    (hW : ∀ x ∈ (W.1 : Set X), x ∉ (J.support : Set X)) : J.ideal W = ⊤ := by
  apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
  have hempty : X.zeroLocus (U := W.1) (J.ideal W) ∩ (W.1 : Set X) = ∅ := by
    rw [← Scheme.IdealSheafData.coe_support_inter]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hx hxW => hW x hxW hx
  have himage := W.2.fromSpec_image_zeroLocus (J.ideal W)
  rw [hempty] at himage
  exact Set.image_eq_empty.mp himage

/-- The ideal sheaf of the closed complement of `U` is the unit ideal on every affine open
contained in `U`. -/
lemma closedIdeal_compl_ideal_eq_top (U : X.Opens) (W : X.affineOpens)
    (hWU : W.1 ≤ U) :
    (closedIdeal ⟨(U : Set X)ᶜ, isClosed_compl_iff.mpr U.2⟩).ideal W = ⊤ := by
  refine ideal_eq_top_of_notMem_support _ W fun x hxW hx => ?_
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hx
  exact hx (hWU hxW)

/-! ### Sections of a submodule which exhaust the ambient module -/

/-- A submodule whose sections exhaust the ambient module on every open contained in `U` has
invertible inclusion after restriction to `U`. -/
lemma isIso_restrictFunctor_map_submodule_ι {K : X.Modules} (P : K.Submodule)
    (U : X.Opens) (hP : ∀ W : X.Opens, W ≤ U → P.toSubmodule.obj (op W) = ⊤) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map P.ι) :=
  isIso_restrictFunctor_map_of_forall_app P.ι U fun W hW =>
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨fun _ _ hab => Subtype.ext hab,
        fun s => ⟨⟨s, (hP W hW).ge Submodule.mem_top⟩, rfl⟩⟩

/-- The sections of `ℐ ^ n K` over an open on which `ℐ` is the unit ideal are all of `K`'s. -/
lemma idealPowSmul_obj_eq_top (J : X.IdealSheafData) (n : ℕ) (K : X.Modules)
    [K.IsQuasicoherent] (U : X.Opens)
    (hJ : ∀ W : X.affineOpens, W.1 ≤ U → J.ideal W = ⊤) (W : X.Opens) (hWU : W ≤ U) :
    (idealPowSmul J n K).toSubmodule.obj (op W) = ⊤ :=
  localSections_idealPowFamily_eq_top J n K fun V hV => hJ V (hV.trans hWU)

/-! ### The separation argument -/

/-- **The separation step.** Let `p : K ⟶ F` be a morphism of coherent modules on a Noetherian
scheme which restricts to an isomorphism over an open `U`. Then `K` has a coherent submodule
`P` which still agrees with `K` over `U` and for which `P ⟶ K ⟶ F` is a monomorphism.

`P` is an ideal power `ℐ ^ m K` for `ℐ` the ideal sheaf of the closed complement of `U`: the
sectionwise kernel of `p` is supported in that closed set, so a power of `ℐ` annihilates it,
and Artin–Rees then separates it from a sufficiently high power of `ℐ` acting on `K`. -/
theorem exists_coherent_submodule_of_isIso_restrict [IsNoetherian X] (F K : X.Modules)
    [F.IsCoherent] [K.IsCoherent] (U : X.Opens) (p : K ⟶ F)
    (hp : IsIso ((Scheme.Modules.restrictFunctor U.ι).map p)) :
    ∃ P : K.Submodule, P.toSheafOfModules.IsCoherent ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map P.ι) ∧ Mono (P.ι ≫ p) := by
  classical
  set J := closedIdeal ⟨(U : Set X)ᶜ, isClosed_compl_iff.mpr U.2⟩ with hJ
  have hKqc : K.IsQuasicoherent := isQuasicoherent_of_isCoherent K
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  -- the sectionwise kernel of `p` vanishes on every open contained in `U`
  have hker : ∀ W : X.Opens, W ≤ U → (kernelSubmodule p).toSubmodule.obj (op W) = ⊥ := by
    intro W hW
    rw [kernelSubmodule_toSubmodule_obj, LinearMap.ker_eq_bot]
    exact ((ConcreteCategory.isIso_iff_bijective _).1
      (isIso_app_of_isIso_restrictFunctor_map p U hp W hW)).1
  have hLqc : (kernelSubmodule p).toSheafOfModules.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubmoduleIso p).symm inferInstance
  have hLcoh : (kernelSubmodule p).toSheafOfModules.IsCoherent :=
    isCoherent_of_isQuasicoherent_submodule K _ hLqc
  -- so it is supported in the closed complement of `U`
  have hsupp : SheafOfModules.supp (kernelSubmodule p).toSheafOfModules ⊆
      (J.support : Set X) := by
    intro x hx
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    intro hxU
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
    refine notMem_supp_of_smul_eq_zero K _ hLqc ⟨V, hV⟩ x hxV 1 ?_ ?_ hx
    · intro h
      have hprime : ((⟨V, hV⟩ : X.affineOpens).2.primeIdealOf ⟨x, hxV⟩).asIdeal.IsPrime :=
        inferInstance
      exact hprime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [one_smul]
      have hzero : ∀ y ∈ (kernelSubmodule p).toSubmodule.obj (op (V : X.Opens)), y = 0 :=
        fun y hy => (Submodule.mem_bot _).1 ((hker V hVU).le hy)
      exact hzero m hm
  -- a power of the ideal annihilates the kernel
  obtain ⟨n, hn₀⟩ := (exists_idealPowerMultiple_eq_bot_iff_supp_subset
    (kernelSubmodule p).toSheafOfModules J).2 hsupp
  have hn := (idealPowerMultiple_eq_bot_iff J n (kernelSubmodule p).toSheafOfModules).1 hn₀
  have hJqc : (kernelSubmodule (SheafOfModules.unitToPushforwardObjUnit
      J.subschemeι.toRingCatSheafHom)).toSheafOfModules.IsQuasicoherent :=
    idealKernel_isQuasicoherent _
  -- Artin-Rees separates it from a higher power
  obtain ⟨m, hm⟩ := exists_idealPow_smul_inf_eq_bot K (kernelSubmodule p)
    (kernelSubmodule (SheafOfModules.unitToPushforwardObjUnit
      J.subschemeι.toRingCatSheafHom))
    n (by
      intro V
      rw [kernelSubmodule_obj_affine]
      refine le_antisymm (Submodule.smul_le.2 fun a ha s hs => ?_) bot_le
      have h3 := (Submodule.eq_bot_iff _).1 (hn V)
      have h4 := h3 _ (Submodule.smul_mem_smul ha (Submodule.mem_top (x := ⟨s, hs⟩)))
      exact (Submodule.mem_bot _).2 (congrArg Subtype.val h4))
  refine ⟨idealPowSmul J m K, isCoherent_idealPowSmul _ m K,
    isIso_restrictFunctor_map_submodule_ι _ U (fun W hW =>
      idealPowSmul_obj_eq_top _ m K U (closedIdeal_compl_ideal_eq_top U) W hW), ?_⟩
  -- the inclusion into `F` is a monomorphism, because an affine section of its kernel lies in
  -- both the ideal power and the kernel of `p`
  refine mono_of_val_app_injective _ fun W a b hab => ?_
  refine Subtype.ext (sub_eq_zero.1 ?_)
  have hd0 : (a.1 - b.1 : K.val.obj W) ∈ (kernelSubmodule p).toSubmodule.obj W := by
    rw [kernelSubmodule_toSubmodule_obj, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact hab
  have hdP : (a.1 - b.1 : K.val.obj W) ∈ (idealPowSmul J m K).toSubmodule.obj W :=
    Submodule.sub_mem _ a.2 b.2
  have hbot := mem_submodule_of_affine (⊥ : K.Submodule) W.unop
    (a.1 - b.1) fun V i => by
      have h1 := (idealPowSmul J m K).toSubmodule.map_mem i.op hdP
      have h2 := (kernelSubmodule p).toSubmodule.map_mem i.op hd0
      have hinf := hm V
      rw [kernelSubmodule_obj_affine, ← obj_idealPowSmul J m K V] at hinf
      exact (SheafOfModules.Submodule.bot_obj K (op (V : X.Opens))).ge
        (hinf ▸ Submodule.mem_inf.2 ⟨h1, h2⟩)
  exact (Submodule.mem_bot _).1
    ((SheafOfModules.Submodule.bot_obj K (op W.unop)).le hbot)

/-! ### The extension -/

/-- **Stacks Project, Tag 0FD0 for a Noetherian scheme.** Let `F` be a coherent and `G` a
quasi-coherent module on a Noetherian scheme `X`, and let `φ : F|_U ⟶ G|_U` be a morphism over
an open subscheme `U`. Then there is a coherent submodule `F' ⟶ F` agreeing with `F` over `U`
and a morphism `F' ⟶ G` whose restriction to `U` is `φ` under that agreement.

The submodule is presented as a monomorphism `i : F' ⟶ F` whose restriction to `U` is an
isomorphism `e`; the two equations say that `e` is that restriction and that `φ` is the
restriction of `φ'` read through `e`. -/
theorem exists_coherent_submodule_extension_of_isNoetherian [IsNoetherian X]
    (F G : X.Modules) [F.IsCoherent] [G.IsQuasicoherent] (U : X.Opens)
    (φ : F.restrict U.ι ⟶ G.restrict U.ι) :
    ∃ (F' : X.Modules) (_ : F'.IsCoherent) (i : F' ⟶ F) (_ : Mono i)
      (φ' : F' ⟶ G) (e : F'.restrict U.ι ≅ F.restrict U.ι),
      (Scheme.Modules.restrictFunctor U.ι).map i = e.hom ∧
        e.hom ≫ φ = (Scheme.Modules.restrictFunctor U.ι).map φ' := by
  classical
  have hFqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hqs : QuasiSeparatedSpace X := ⟨fun _ _ _ _ _ _ => NoetherianSpace.isCompact _⟩
  -- the graph of `φ` is a finite-type quasi-coherent subobject of `(F ⊞ G)|_U`
  have hRF : ((Scheme.Modules.restrictFunctor U.ι).obj F).IsCoherent :=
    AlgebraicGeometry.Modules.isCoherent_restrict F U
  have hgIso := isIso_graphSubobject_arrow_comp_fst F G U φ
  have hgqc : ((Subobject.mk (graphHom F G U φ) :
      Subobject ((F ⊞ G).restrict U.ι)) : U.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (graphHom F G U φ)).symm (isQuasicoherent_of_isCoherent _)
  have hRFft : ((Scheme.Modules.restrictFunctor U.ι).obj F).IsFiniteType :=
    SheafOfModules.IsCoherent.isFiniteType
  have hgft : ((Subobject.mk (graphHom F G U φ) :
      Subobject ((F ⊞ G).restrict U.ι)) : U.toScheme.Modules).IsFiniteType :=
    isFiniteType_of_iso_modules (Subobject.underlyingIso (graphHom F G U φ)) hRFft
  -- extend it over the quasi-compact `X`
  obtain ⟨Q, hQqc, hQft, eQ, heQ⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension (F ⊞ G) U
      (NoetherianSpace.isCompact _) (Subobject.mk (graphHom F G U φ))
  have hQqc' : (Q : X.Modules).IsQuasicoherent := hQqc
  have hQft' : (Q : X.Modules).IsFiniteType := hQft
  have hQcoh : (Q : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType
      (F := (Q : X.Modules))
  -- the first projection is an isomorphism over `U`
  set f : (Q : X.Modules) ⟶ F := Q.arrow ≫ biprod.fst with hf
  set g : (Q : X.Modules) ⟶ G := Q.arrow ≫ biprod.snd with hg
  have hfst : (Scheme.Modules.restrictFunctor U.ι).map f =
      eQ.hom ≫ (Subobject.mk (graphHom F G U φ)).arrow ≫
        (Scheme.Modules.restrictFunctor U.ι).map biprod.fst := by
    rw [hf, Functor.map_comp, heQ, Category.assoc]
  have hp : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
    rw [hfst]
    exact IsIso.comp_isIso' inferInstance hgIso
  -- the two projections agree on the graph
  have hkey : (Scheme.Modules.restrictFunctor U.ι).map f ≫ φ =
      (Scheme.Modules.restrictFunctor U.ι).map g := by
    rw [hfst, hg, Functor.map_comp, heQ]
    simp only [Category.assoc]
    rw [graphSubobject_arrow_comp_snd]
  -- separate the kernel away
  obtain ⟨P, hPcoh, hPiso, hPmono⟩ :=
    exists_coherent_submodule_of_isIso_restrict F (Q : X.Modules) U f hp
  have hmapf := Functor.map_comp (Scheme.Modules.restrictFunctor U.ι) P.ι f
  have hiIso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (P.ι ≫ f)) := by
    rw [hmapf]
    exact IsIso.comp_isIso' hPiso hp
  refine ⟨P.toSheafOfModules, hPcoh, P.ι ≫ f, hPmono, P.ι ≫ g,
    asIso ((Scheme.Modules.restrictFunctor U.ι).map (P.ι ≫ f)), rfl, ?_⟩
  change (Scheme.Modules.restrictFunctor U.ι).map (P.ι ≫ f) ≫ φ =
    (Scheme.Modules.restrictFunctor U.ι).map (P.ι ≫ g)
  rw [hmapf, Functor.map_comp (Scheme.Modules.restrictFunctor U.ι) P.ι g, Category.assoc,
    hkey]

end AlgebraicGeometry

end
