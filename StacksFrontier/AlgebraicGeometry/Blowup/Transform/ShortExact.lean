module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.QuotSMulTop
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Flatness.QuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Localization
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.QcohShortExact.QcohExtension
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent

/-!
# Short exactness of strict transforms

Let `f : X ⟶ S` be a morphism of schemes and let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact
sequence of quasi-coherent `𝒪_X`-modules which remains short exact after every base change
`T ⟶ S`. Then the strict transforms of the three modules along the blowup of `S` in a
quasi-coherent ideal again form a short exact sequence, and the three maps are the ones induced
by the quotient maps onto the strict transforms.

## Main results

* `AlgebraicGeometry.strictTransformSheaf_shortExact`: the short exact sequence of strict
  transforms, with its two maps pinned down by the quotient maps onto the strict transforms.

## Implementation notes

The strict transform of a module is the quotient of its pullback to `X ×_S S'` by the submodule
of sections supported on the preimage of the centre, so the two maps are obtained from the
functoriality of the cokernel; the compatibility of a morphism with supported sections is
`AlgebraicGeometry.Scheme.Modules.map_mem_supportedSectionsSubmodule`, and the two compatibility
equations are then `CategoryTheory.Limits.cokernel.π_desc`. Monomorphy on the left holds because
a section of `F₁` whose image in `F₂` is supported on the centre is itself supported there, and
surjectivity on the right is formal.

Exactness in the middle is the only step with content, and it reduces to the surjectivity of
the induced map on the submodules of supported sections. That is checked on a basis of affine
opens of `X ×_S S'` on which the exceptional divisor is cut out by a single function `a` — such
a basis exists because the exceptional ideal is an effective Cartier divisor
([Stacks, Tag 02OS]) and the affine charts of [Stacks, Tag 07ZU] are available as
`Stacks.Divisors.exists_affineOpen_basicOpen_eq_inf_compl_support`. Over such a chart the
sections supported on the divisor are exactly the `a`-power torsion ([Stacks, Tag 07ZP]), the
sections of the sequence are exact with surjective last map
(`Stacks.AlgebraicGeometry.QcohExtension.surjective_app_of_shortExact` together with the left
exactness of `Γ(U, -)`), and the algebra is the lifting argument of the source: an element of
`Γ(F₃, U)` killed by `a ^ n` lifts to one of `Γ(F₂, U)` killed by `a ^ n`, using that a section
of `F₁` whose image is divisible by `a ^ n` is itself divisible by `a ^ n`.

That divisibility is where the universal short exactness enters. Base changing `S` along the
closed subscheme cut out by `a ^ n` turns it into the statement that reduction modulo `a ^ n` is
injective on `Γ(F₁, U)`, and the sections of the base changed module are the extension of
scalars of the sections (`AlgebraicGeometry.quasicoherentPullbackSectionsIso`, whose naturality
is read off from its normalisation on `1 ⊗ m`). The affine square exhibiting the base change is
`Stacks.Flatness.isPullback_SpecMap_quotient`.

## References

* [Stacks Project, Tag 080W](https://stacks.math.columbia.edu/tag/080W)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Pointwise ChangeOfRings

namespace AlgebraicGeometry

universe u

/-! ### The algebra of divisibility and power torsion -/

/-- If reduction modulo `b` is injective on `f`, then an element of the source whose image is
divisible by `b` is itself divisible by `b`. -/
private lemma exists_eq_smul_of_injective_quotSMulTop {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (b : R) (φ : M →ₗ[R] N) (hφ : Function.Injective (QuotSMulTop.map b φ))
    (x : M) (y : N) (hxy : φ x = b • y) : ∃ z : M, x = b • z := by
  have h0 : QuotSMulTop.map b φ (Submodule.Quotient.mk x) = 0 := by
    rw [QuotSMulTop.map_apply_mk, hxy]
    exact (Submodule.Quotient.mk_eq_zero _).2
      ((Submodule.mem_smul_pointwise_iff_exists (b • y) b ⊤).2 ⟨y, trivial, rfl⟩)
  obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists x b ⊤).1
    ((Submodule.Quotient.mk_eq_zero _).1 (hφ (h0.trans (map_zero _).symm)))
  exact ⟨z, hz.symm⟩

/-- Reduction modulo `b` is injective on `φ` as soon as tensoring with `R ⧸ (b)` is. -/
private lemma injective_quotSMulTop_map_of_injective_lTensor {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (b : R) (φ : M →ₗ[R] N)
    (hφ : Function.Injective (φ.lTensor (R ⧸ Ideal.span {b}))) :
    Function.Injective (QuotSMulTop.map b φ) := by
  intro x y hxy
  refine (QuotSMulTop.equivQuotTensor b M).injective (hφ ?_)
  have h := QuotSMulTop.equivQuotTensor_naturality b φ
  calc φ.lTensor (R ⧸ Ideal.span {b}) (QuotSMulTop.equivQuotTensor b M x)
      = QuotSMulTop.equivQuotTensor b N (QuotSMulTop.map b φ x) :=
        (LinearMap.congr_fun h x).symm
    _ = QuotSMulTop.equivQuotTensor b N (QuotSMulTop.map b φ y) := by rw [hxy]
    _ = φ.lTensor (R ⧸ Ideal.span {b}) (QuotSMulTop.equivQuotTensor b M y) :=
        LinearMap.congr_fun h y

/-- **The lifting step of the Stacks argument.** Let `0 → M₁ → M₂ → M₃ → 0` be an exact
sequence in which the image of every element of `M₁` divisible by `a ^ n` is itself divisible by
`a ^ n`. Then every element of `M₃` killed by a power of `a` lifts to an element of `M₂` killed
by a power of `a`. -/
private lemma exists_preimage_pow_smul_eq_zero {R M₁ M₂ M₃ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (a : R) (φ : M₁ →ₗ[R] M₂) (ψ : M₂ →ₗ[R] M₃)
    (hex : Function.Exact φ ψ) (hψ : Function.Surjective ψ)
    (hdvd : ∀ (n : ℕ) (x : M₁) (y : M₂), φ x = a ^ n • y → ∃ z : M₁, x = a ^ n • z)
    (y : M₃) (hy : ∃ n : ℕ, a ^ n • y = 0) :
    ∃ x : M₂, (∃ n : ℕ, a ^ n • x = 0) ∧ ψ x = y := by
  obtain ⟨x, rfl⟩ := hψ y
  obtain ⟨n, hn⟩ := hy
  obtain ⟨z, hz⟩ := (hex (a ^ n • x)).mp (by simpa only [map_smul] using hn)
  obtain ⟨w, hw⟩ := hdvd n z x hz
  refine ⟨x - φ w, ⟨n, ?_⟩, ?_⟩
  · rw [smul_sub, ← φ.map_smul, ← hw, hz, sub_self]
  · rw [map_sub, (hex (φ w)).mpr ⟨w, rfl⟩, sub_zero]

/-! ### Supported sections on an affine chart -/

/-- Restriction of a section to two opens that happen to be equal vanishes simultaneously. -/
private lemma res_eq_zero_iff_of_eq {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
    (hVW : V = W) (hV : V ≤ U) (hW : W ≤ U) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE hV).op s = 0 ↔ F.presheaf.map (homOfLE hW).op s = 0 := by
  subst hVW
  rfl

/-- On an affine open on which the complement of `Z` is the basic open of `a`, a section of a
quasi-coherent module is supported on `Z` exactly when a power of `a` kills it. This is the
torsion description of supported sections used by [Stacks, Tag 07ZP], in the one-element case;
`AlgebraicGeometry.mem_supportedSectionsSubmodule_iff_exists_pow_le_annihilator` is the form for
a finitely generated ideal. -/
lemma mem_supportedSectionsSubmodule_iff_exists_pow_smul_eq_zero
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U)) {Z : Set X} (hZ : (X.basicOpen a : Set X) = (U : Set X) ∩ Zᶜ)
    (s : Γ(F, U)) :
    s ∈ (Scheme.Modules.supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      ∃ n : ℕ, a ^ n • s = 0 := by
  have hcompl : s ∈ (Scheme.Modules.supportedSectionsSubmodule Z F).toSubmodule.obj (op U) ↔
      s ∈ (Scheme.Modules.supportedSectionsSubmodule
        ((X.basicOpen a : Set X))ᶜ F).toSubmodule.obj (op U) := by
    rw [Scheme.Modules.mem_supportedSectionsSubmodule_iff,
      Scheme.Modules.mem_supportedSectionsSubmodule_iff]
    exact ⟨fun h x hx hxb => h x hx (hZ ▸ not_not.mp hxb).2,
      fun h x hx hxZ => h x hx fun hc => hc (hZ ▸ ⟨hx, hxZ⟩)⟩
  rw [hcompl, Scheme.Modules.mem_supportedSectionsSubmodule_compl_iff_restrict_eq_zero,
    res_eq_zero_iff_of_eq F (inf_eq_right.mpr (X.basicOpen_le a)) inf_le_left
      (X.basicOpen_le a) s]
  refine ⟨Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero F hU a s, ?_⟩
  rintro ⟨n, hn⟩
  have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ n)) := by
    rw [map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen a).pow n
  refine hunit.smul_eq_zero.mp ?_
  rw [← Scheme.Modules.map_smul, hn, map_zero]

/-! ### The induced morphism between submodules of supported sections -/

/-- A morphism of sheaves of modules restricts to a morphism between the submodules of sections
supported on a subset. -/
private def supportedSectionsObjMap {X : Scheme.{u}} (Z : Set X) {F G : X.Modules} (φ : F ⟶ G) :
    Scheme.Modules.supportedSectionsObj Z F ⟶ Scheme.Modules.supportedSectionsObj Z G :=
  ⟨{ app V := ModuleCat.ofHom ((φ.val.app V).hom.restrict
       (p := (Scheme.Modules.supportedSectionsSubmodule Z F).toSubmodule.obj V)
       (q := (Scheme.Modules.supportedSectionsSubmodule Z G).toSubmodule.obj V)
       (fun s hs => Scheme.Modules.map_mem_supportedSectionsSubmodule Z φ V.unop s hs))
     naturality := by
       intro U V i
       ext s
       exact Subtype.ext (PresheafOfModules.naturality_apply φ.val i s.val) }⟩

/-- The induced morphism on supported sections is compatible with the inclusions. -/
private lemma supportedSectionsObjMap_comp_ι {X : Scheme.{u}} (Z : Set X) {F G : X.Modules}
    (φ : F ⟶ G) :
    supportedSectionsObjMap Z φ ≫ Scheme.Modules.supportedSectionsι Z G =
      Scheme.Modules.supportedSectionsι Z F ≫ φ := by
  ext U s
  rfl

/-- A morphism of modules composed with the quotient by the supported sections kills the
supported sections of its source. -/
private lemma supportedSectionsι_comp_comp_cokernel_π {X : Scheme.{u}} (Z : Set X)
    {F G : X.Modules} (φ : F ⟶ G) :
    Scheme.Modules.supportedSectionsι Z F ≫ φ ≫
      cokernel.π (Scheme.Modules.supportedSectionsι Z G) = 0 := by
  rw [← Category.assoc, ← supportedSectionsObjMap_comp_ι, Category.assoc, cokernel.condition,
    comp_zero]

/-- Being supported on a subset is reflected by a monomorphism. -/
private lemma mem_supportedSectionsSubmodule_of_map_mem {X : Scheme.{u}} (Z : Set X)
    {F G : X.Modules} (φ : F ⟶ G) [Mono φ] (U : X.Opens) (s : Γ(F, U))
    (hs : φ.app U s ∈ (Scheme.Modules.supportedSectionsSubmodule Z G).toSubmodule.obj (op U)) :
    s ∈ (Scheme.Modules.supportedSectionsSubmodule Z F).toSubmodule.obj (op U) := by
  rw [Scheme.Modules.mem_supportedSectionsSubmodule_iff] at hs ⊢
  intro x hx hxZ
  obtain ⟨W, hxW, iU, iV, hres⟩ := TopCat.Presheaf.germ_eq G.val.presheaf x hx hx (φ.app U s) 0
    ((hs x hx hxZ).trans (map_zero _).symm)
  obtain rfl : iU = iV := Subsingleton.elim _ _
  have hzero : F.presheaf.map iU.op s = 0 := by
    refine Stacks.AlgebraicGeometry.CardinalGeneration.injective_app_of_mono φ W ?_
    rw [map_zero, show φ.app W (F.presheaf.map iU.op s) = G.presheaf.map iU.op (φ.app U s) from
      PresheafOfModules.naturality_apply φ.val iU.op s]
    exact hres.trans (map_zero _)
  exact (TopCat.Presheaf.germ_ext (F := F.val.presheaf) (U := U) (V := U) (x := x)
    (hxU := hx) (hxV := hx) W hxW iU iU (hzero.trans (map_zero _).symm)).trans (map_zero _)

/-! ### Epimorphisms detected on a basis -/

/-- A morphism of `𝒪_X`-modules surjective on sections over every open of a basis is an
epimorphism. -/
private lemma epi_of_surjective_app_on_basis {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (B : Set X.Opens) (hB : Opens.IsBasis B)
    (hφ : ∀ U ∈ B, Function.Surjective (φ.app U)) : Epi φ := by
  apply (SheafOfModules.toSheaf.{u} X.ringCatSheaf).epi_of_epi_map
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi (X := X.carrier)
    ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ)).mp
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s x hx
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
  exact ⟨V, hVU, hφ V hV _, hxV⟩

/-! ### Monomorphy and exactness of the quotients by supported sections -/

/-- The morphism induced on the quotients by the supported sections by a monomorphism is a
monomorphism: the sections of the source supported on `Z` are exactly those whose image is. -/
private lemma mono_cokernel_desc_supportedSections {X : Scheme.{u}} (Z : Set X)
    {F G : X.Modules} (φ : F ⟶ G) [Mono φ]
    (w : Scheme.Modules.supportedSectionsι Z F ≫
      φ ≫ cokernel.π (Scheme.Modules.supportedSectionsι Z G) = 0) :
    Mono (cokernel.desc (Scheme.Modules.supportedSectionsι Z F)
      (φ ≫ cokernel.π (Scheme.Modules.supportedSectionsι Z G)) w) := by
  let ιF := Scheme.Modules.supportedSectionsι Z F
  let ιG := Scheme.Modules.supportedSectionsι Z G
  let L : ShortComplex X.Modules := ShortComplex.mk ιF (φ ≫ cokernel.π ιG) w
  have hLexact : L.Exact := by
    refine L.exact_of_f_is_kernel (KernelFork.IsLimit.ofι' _ _ ?_)
    intro A k hk
    have hk' : (k ≫ φ) ≫ cokernel.π ιG = 0 := (Category.assoc _ _ _).trans hk
    let l := (ShortComplex.exact_cokernel ιG).lift (k ≫ φ) hk'
    have hmem (V : X.Opens) (s : Γ(A, V)) : k.app V s ∈
        (Scheme.Modules.supportedSectionsSubmodule Z F).toSubmodule.obj (op V) := by
      refine mem_supportedSectionsSubmodule_of_map_mem Z φ V _ ?_
      have hh := congrArg (fun m : A ⟶ G => m.app V s) ((ShortComplex.exact_cokernel ιG).lift_f
        (k ≫ φ) hk')
      change (l.app V s).val = φ.app V (k.app V s) at hh
      rw [← hh]
      exact (l.app V s).property
    let lF : A ⟶ Scheme.Modules.supportedSectionsObj Z F :=
      ⟨{ app V := ModuleCat.ofHom
          { toFun s := ⟨k.val.app V s, hmem V.unop s⟩
            map_add' _ _ := Subtype.ext (map_add _ _ _)
            map_smul' _ _ := Subtype.ext (map_smul _ _ _) }
         naturality := by
           intro U V i
           ext s
           exact Subtype.ext (PresheafOfModules.naturality_apply k.val i s) }⟩
    refine ⟨lF, ?_⟩
    ext V s
    rfl
  exact hLexact.mono_cokernelDesc

/-- **Exactness in the middle for the quotients by supported sections.** Given a short exact
sequence of `𝒪_X`-modules whose induced morphism on sections supported on `Z` is an
epimorphism, the induced sequence of quotients by the supported sections is exact. -/
private lemma exact_cokernel_supportedSections {X : Scheme.{u}} (Z : Set X)
    (C : ShortComplex X.Modules) (hC : C.Exact) [Epi C.g]
    [Epi (supportedSectionsObjMap Z C.g)]
    (f' : cokernel (Scheme.Modules.supportedSectionsι Z C.X₁) ⟶
      cokernel (Scheme.Modules.supportedSectionsι Z C.X₂))
    (g' : cokernel (Scheme.Modules.supportedSectionsι Z C.X₂) ⟶
      cokernel (Scheme.Modules.supportedSectionsι Z C.X₃))
    (w : f' ≫ g' = 0)
    (hf : cokernel.π (Scheme.Modules.supportedSectionsι Z C.X₁) ≫ f' =
      C.f ≫ cokernel.π (Scheme.Modules.supportedSectionsι Z C.X₂))
    (hg : cokernel.π (Scheme.Modules.supportedSectionsι Z C.X₂) ≫ g' =
      C.g ≫ cokernel.π (Scheme.Modules.supportedSectionsι Z C.X₃)) :
    (ShortComplex.mk f' g' w).Exact := by
  have : Epi g' := epi_of_epi_fac hg
  refine ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ' _ _ ?_)
  intro A k hk
  have hpre : C.f ≫ (cokernel.π (Scheme.Modules.supportedSectionsι Z C.X₂) ≫ k) = 0 := by
    rw [← Category.assoc, ← hf, Category.assoc, hk, comp_zero]
  have ha : C.g ≫ hC.desc (cokernel.π (Scheme.Modules.supportedSectionsι Z C.X₂) ≫ k) hpre =
      cokernel.π (Scheme.Modules.supportedSectionsι Z C.X₂) ≫ k := hC.g_desc _ _
  have hTa : Scheme.Modules.supportedSectionsι Z C.X₃ ≫
      hC.desc (cokernel.π (Scheme.Modules.supportedSectionsι Z C.X₂) ≫ k) hpre = 0 := by
    refine (cancel_epi (supportedSectionsObjMap Z C.g)).mp ?_
    rw [← Category.assoc, supportedSectionsObjMap_comp_ι, Category.assoc, ha, ← Category.assoc,
      cokernel.condition, zero_comp, comp_zero]
  refine ⟨cokernel.desc _ _ hTa, ?_⟩
  refine (cancel_epi (cokernel.π (Scheme.Modules.supportedSectionsι Z C.X₂))).mp ?_
  rw [← Category.assoc, hg, Category.assoc, cokernel.π_desc, ha]

/-! ### Transport of short exactness along pullbacks -/

/-- Short exactness of the image of a sequence under a functor transports along an isomorphism of
functors. -/
private lemma shortExact_map_of_iso {X Y : Scheme.{u}} {F G : X.Modules ⥤ Y.Modules}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (e : F ≅ G)
    (C : ShortComplex X.Modules) (h : (C.map F).ShortExact) :
    (C.map G).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso (C.mapNatIso e)).mp h

/-- Pulling back along an open immersion preserves short exactness: restriction along an open
immersion is exact, and the pullback is isomorphic to it. -/
private lemma shortExact_map_pullback_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (C : ShortComplex Y.Modules) (hC : C.ShortExact) :
    (C.map (Scheme.Modules.pullback j)).ShortExact :=
  shortExact_map_of_iso (Scheme.Modules.restrictFunctorIsoPullback j) C
    (hC.map_of_exact (Scheme.Modules.restrictFunctor j))

/-- Short exactness of the pullback to a chosen pullback square transports to any other
realisation of that square. -/
private lemma shortExact_map_pullback_of_isPullback {X S T Y : Scheme.{u}} {f : X ⟶ S}
    {g : T ⟶ S} {p : Y ⟶ X} {q : Y ⟶ T} (h : IsPullback p q f g)
    (C : ShortComplex X.Modules)
    (hC : (C.map (Scheme.Modules.pullback (pullback.fst f g))).ShortExact) :
    (C.map (Scheme.Modules.pullback p)).ShortExact := by
  have h'' : (C.map (Scheme.Modules.pullback (pullback.fst f g) ⋙
      Scheme.Modules.pullback h.isoPullback.hom)).ShortExact :=
    shortExact_map_pullback_of_isOpenImmersion h.isoPullback.hom _ hC
  exact shortExact_map_of_iso (Scheme.Modules.pullbackComp h.isoPullback.hom (pullback.fst f g) ≪≫
    Scheme.Modules.pullbackCongr h.isoPullback_hom_fst) C h''

/-- A sequence that stays short exact after every base change of the base stays short exact
after a further base change of an already performed one. -/
private lemma shortExact_map_pullback_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    (C : ShortComplex X.Modules)
    (hC : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (C.map (Scheme.Modules.pullback (pullback.fst f g))).ShortExact)
    {B T : Scheme.{u}} (b : B ⟶ S) (t : T ⟶ B) :
    ((C.map (Scheme.Modules.pullback (pullback.fst f b))).map
      (Scheme.Modules.pullback (pullback.fst (pullback.snd f b) t))).ShortExact :=
  shortExact_map_of_iso (Scheme.Modules.pullbackComp (pullback.fst (pullback.snd f b) t)
    (pullback.fst f b)).symm C (shortExact_map_pullback_of_isPullback
        ((IsPullback.of_hasPullback (pullback.snd f b) t).paste_horiz
          (IsPullback.of_hasPullback f b)) C (hC (t ≫ b)))

/-- Restricting to an open of `X` and then base changing along a morphism to `S` preserves short
exactness, for a sequence that stays short exact after every base change of `S`. -/
private lemma shortExact_map_pullback_restrict_of_isPullback {X S V T W : Scheme.{u}}
    (f : X ⟶ S) (j : V ⟶ X) [IsOpenImmersion j] (t : T ⟶ S) (p : W ⟶ V) (q : W ⟶ T)
    (h : IsPullback p q (j ≫ f) t) (C : ShortComplex X.Modules)
    (hC : (C.map (Scheme.Modules.pullback (pullback.fst f t))).ShortExact) :
    ((C.map (Scheme.Modules.pullback j)).map (Scheme.Modules.pullback p)).ShortExact := by
  let k : W ⟶ pullback f t :=
    pullback.lift (p ≫ j) q (by simpa only [Category.assoc] using h.w)
  have hsnd : k ≫ pullback.snd f t = q := pullback.lift_snd _ _ _
  have hfac : k ≫ pullback.fst f t = p ≫ j := pullback.lift_fst _ _ _
  have hk : IsPullback p k j (pullback.fst f t) :=
    IsPullback.of_bot (by rwa [hsnd]) hfac.symm (IsPullback.of_hasPullback f t)
  have : IsOpenImmersion k := MorphismProperty.of_isPullback hk inferInstance
  exact shortExact_map_of_iso (Scheme.Modules.pullbackComp k (pullback.fst f t) ≪≫
    Scheme.Modules.pullbackCongr hfac ≪≫ (Scheme.Modules.pullbackComp p j).symm) C
    (shortExact_map_pullback_of_isOpenImmersion k _ hC)

/-! ### Sections of a pullback over an affine chart -/

/-- `AlgebraicGeometry.quasicoherentPullbackSectionsIso` is natural in the module: both sides
send `1 ⊗ m` to the pullback of `m`, by naturality of the unit of `(Spec φ)^* ⊣ (Spec φ)_*`. -/
private lemma quasicoherentPullbackSectionsIso_naturality (R S : CommRingCat.{u}) (φ : R ⟶ S)
    {F G : (Spec R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : F ⟶ G) :
    (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map ψ) ≫
        (quasicoherentPullbackSectionsIso R S φ G).hom =
      (quasicoherentPullbackSectionsIso R S φ F).hom ≫
        moduleSpecΓFunctor.map ((Scheme.Modules.pullback (Spec.map φ)).map ψ) := by
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  have h₁ := ConcreteCategory.comp_apply
    ((ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map ψ))
    (quasicoherentPullbackSectionsIso R S φ G).hom ((1 : S) ⊗ₜ[R, φ.hom] m)
  have h₂ := ConcreteCategory.comp_apply
    (quasicoherentPullbackSectionsIso R S φ F).hom
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback (Spec.map φ)).map ψ))
    ((1 : S) ⊗ₜ[R, φ.hom] m)
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  exact (quasicoherentPullbackSectionsIso_hom_one_tmul R S φ G
      (moduleSpecΓFunctor.map ψ m)).trans
    ((Scheme.Modules.unit_app_val_app_naturality (Spec.map φ) ψ ⊤ m).symm.trans
      (congrArg (ConcreteCategory.hom (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullback (Spec.map φ)).map ψ)))
        (quasicoherentPullbackSectionsIso_hom_one_tmul R S φ F m).symm))

/-- Monomorphy of a pullback along `Spec φ` is inherited by the extension of scalars along `φ`
of the global sections. -/
private lemma injective_extendScalars_map_of_mono_pullback (R S : CommRingCat.{u}) (φ : R ⟶ S)
    {F G : (Spec R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : F ⟶ G)
    [Mono ((Scheme.Modules.pullback (Spec.map φ)).map ψ)] :
    Function.Injective ((ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map ψ)) := by
  have hcomp : Mono ((ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map ψ) ≫
      (quasicoherentPullbackSectionsIso R S φ G).hom) := by
    rw [quasicoherentPullbackSectionsIso_naturality R S φ ψ]
    infer_instance
  rw [← ModuleCat.mono_iff_injective]
  exact mono_of_mono _ (quasicoherentPullbackSectionsIso R S φ G).hom

/-! ### Divisibility of sections over an affine chart -/

/-- Reduction modulo `c` of a linear equivalence is injective. -/
private lemma injective_quotSMulTop_map_toLinearMap {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (c : R) (e : M ≃ₗ[R] N) :
    Function.Injective (QuotSMulTop.map c e.toLinearMap) := by
  intro p q hpq
  have h := congrArg (QuotSMulTop.map c e.symm.toLinearMap) hpq
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← QuotSMulTop.map_comp, e.symm_comp,
    QuotSMulTop.map_id, LinearMap.id_apply, LinearMap.id_apply] at h

/-- Injectivity of a reduction modulo `c` transports along a commuting square of linear
equivalences. -/
private lemma injective_quotSMulTop_map_of_comm {R MF MG NF NG : Type*} [CommRing R]
    [AddCommGroup MF] [Module R MF] [AddCommGroup MG] [Module R MG]
    [AddCommGroup NF] [Module R NF] [AddCommGroup NG] [Module R NG]
    (c : R) (α : MF →ₗ[R] MG) (β : NF →ₗ[R] NG) (eF : MF ≃ₗ[R] NF) (eG : MG ≃ₗ[R] NG)
    (hcomm : β ∘ₗ eF.toLinearMap = eG.toLinearMap ∘ₗ α)
    (hα : Function.Injective (QuotSMulTop.map c α)) :
    Function.Injective (QuotSMulTop.map c β) := by
  have hβ : β = eG.toLinearMap ∘ₗ α ∘ₗ eF.symm.toLinearMap := by
    rw [← LinearMap.comp_assoc, ← hcomm]
    ext x
    simp
  rw [hβ, QuotSMulTop.map_comp, QuotSMulTop.map_comp, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (injective_quotSMulTop_map_toLinearMap c eG).comp
    (hα.comp (injective_quotSMulTop_map_toLinearMap c eF.symm))

/-- The sections of a module over an affine open, compared with the global sections of its
restriction along `hU.fromSpec`, are natural in the module. -/
private lemma affineSectionsLinearEquiv_naturality {X : Scheme.{u}} {F G : X.Modules}
    (ψ : F ⟶ G) {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(F.restrict hU.fromSpec, ⊤)) :
    affineSectionsLinearEquiv G hU
        (((Scheme.Modules.restrictFunctor hU.fromSpec).map ψ).app ⊤ s) =
      ψ.app U (affineSectionsLinearEquiv F hU s) := by
  have he : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  rw [affineSectionsLinearEquiv_eq_map G hU he, affineSectionsLinearEquiv_eq_map F hU he]
  exact (PresheafOfModules.naturality_apply ψ.val (eqToHom he.symm).op s).symm

/-- **Reduction modulo a power is injective on sections over an affine open.** If the morphism
`ψ` stays a monomorphism after base change to the closed subscheme of `Spec Γ(X, V)` cut out by
`c`, then reduction modulo `c` is injective on the sections over `V`. -/
private lemma injective_quotSMulTop_map_app_of_mono_pullback {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : F ⟶ G) (c : Γ(X, V))
    (hmono : Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {c}))))).map
      ((Scheme.Modules.restrictFunctor hV.fromSpec).map ψ))) :
    Function.Injective (QuotSMulTop.map c (Stacks.AlgebraicGeometry.QcohLimits.appₗ ψ V)) := by
  refine injective_quotSMulTop_map_of_comm c
    (moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor hV.fromSpec).map ψ)).hom _
    (affineSectionsLinearEquiv F hV) (affineSectionsLinearEquiv G hV) ?_
    (injective_quotSMulTop_map_of_injective_lTensor c _
      (injective_extendScalars_map_of_mono_pullback _ _
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))
        ((Scheme.Modules.restrictFunctor hV.fromSpec).map ψ)))
  exact LinearMap.ext fun s => (affineSectionsLinearEquiv_naturality ψ hV s).symm

/-- **Divisibility of the affine sections of a universally short exact sequence.** Over a
compatible pair of affine opens, a section of `F₁` whose image in `F₂` is divisible by the `n`-th
power of a function pulled back from the base is itself divisible by that power. The input is
the short exactness after base change to the closed subscheme of the base cut out by that
power. -/
private lemma exists_eq_pow_smul_of_universally_shortExact {X S : Scheme.{u}} (f : X ⟶ S)
    (C : ShortComplex X.Modules) [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent]
    (hC : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (C.map (Scheme.Modules.pullback (pullback.fst f g))).ShortExact)
    {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (a : Γ(S, U)) (n : ℕ) (x : Γ(C.X₁, V)) (y : Γ(C.X₂, V))
    (hxy : C.f.app V x = f.appLE U V hVU a ^ n • y) :
    ∃ z : Γ(C.X₁, V), x = f.appLE U V hVU a ^ n • z := by
  have hpb : IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((Ideal.span {a ^ n}).map (f.appLE U V hVU).hom))))
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap
        ((Ideal.span {a ^ n}).map (f.appLE U V hVU).hom)
        (f.appLE U V hVU).hom Ideal.le_comap_map)))
      (hV.fromSpec ≫ f)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ n}))) ≫
        hU.fromSpec) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU]
    exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ hU.fromSpec _
      (Stacks.Flatness.isPullback_SpecMap_quotient (f.appLE U V hVU)
        (Ideal.span {a ^ n})).isLimit)
  have hse' : ((C.map (Scheme.Modules.restrictFunctor hV.fromSpec)).map
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        ((Ideal.span {a ^ n}).map (f.appLE U V hVU).hom)))))).ShortExact :=
    shortExact_map_of_iso (Functor.isoWhiskerRight
      (Scheme.Modules.restrictFunctorIsoPullback hV.fromSpec) _).symm C
      (shortExact_map_pullback_restrict_of_isPullback f hV.fromSpec _ _ _ hpb C (hC _))
  have hideal : (Ideal.span {a ^ n} : Ideal Γ(S, U)).map (f.appLE U V hVU).hom =
      Ideal.span {f.appLE U V hVU a ^ n} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow]
  have hmono := (congrArg (fun I : Ideal Γ(X, V) => Mono ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map
      ((Scheme.Modules.restrictFunctor hV.fromSpec).map C.f))) hideal).mp hse'.mono_f
  exact exists_eq_smul_of_injective_quotSMulTop _ _
    (injective_quotSMulTop_map_app_of_mono_pullback hV C.f _ hmono) x y hxy

/-! ### Surjectivity on supported sections -/

/-- Taking sections over an open is additive: addition of morphisms of `𝒪_X`-modules is
computed on sections. -/
private instance additive_sectionsFunctor {X : Scheme.{u}} (U : X.Opens) :
    (Stacks.AlgebraicGeometry.QcohLimits.sectionsFunctor X U).Additive where
  map_add := rfl

/-- On an affine open, global sections carry a short exact sequence with quasi-coherent first
term to an exact pair of maps with surjective second map. -/
private lemma exact_and_surjective_app_of_shortExact {X : Scheme.{u}}
    (C : ShortComplex X.Modules) (hC : C.ShortExact) [C.X₁.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Exact (Stacks.AlgebraicGeometry.QcohLimits.appₗ C.f U)
        (Stacks.AlgebraicGeometry.QcohLimits.appₗ C.g U) ∧
      Function.Surjective (Stacks.AlgebraicGeometry.QcohLimits.appₗ C.g U) := by
  refine ⟨?_, Stacks.AlgebraicGeometry.QcohExtension.surjective_app_of_shortExact C hC
    inferInstance U hU⟩
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (Stacks.AlgebraicGeometry.QcohLimits.sectionsFunctor X U)).1 inferInstance C hC).1

/-- **The induced morphism on sections supported on `Z` is an epimorphism**, given a basis of
affine opens on which the complement of `Z` is a basic open, the sections of the sequence are
exact and the divisibility criterion of the Stacks argument holds. -/
private lemma epi_supportedSectionsObjMap_of_local_divisibility {X : Scheme.{u}} (Z : Set X)
    (C : ShortComplex X.Modules) [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (B : Set X.Opens) (hB : Opens.IsBasis B)
    (hlocal : ∀ U ∈ B, ∃ (_ : IsAffineOpen U) (a : Γ(X, U)),
      (X.basicOpen a : Set X) = (U : Set X) ∩ Zᶜ ∧
      Function.Exact (Stacks.AlgebraicGeometry.QcohLimits.appₗ C.f U)
        (Stacks.AlgebraicGeometry.QcohLimits.appₗ C.g U) ∧
      Function.Surjective (Stacks.AlgebraicGeometry.QcohLimits.appₗ C.g U) ∧
      (∀ (n : ℕ) (x : Γ(C.X₁, U)) (y : Γ(C.X₂, U)),
        Stacks.AlgebraicGeometry.QcohLimits.appₗ C.f U x = a ^ n • y →
          ∃ z : Γ(C.X₁, U), x = a ^ n • z)) :
    Epi (supportedSectionsObjMap Z C.g) := by
  refine epi_of_surjective_app_on_basis _ B hB fun U hUB t => ?_
  obtain ⟨hU, a, hZ, hex, hsurj, hdvd⟩ := hlocal U hUB
  have ht : ∃ n : ℕ,
      a ^ n • (Scheme.Modules.supportedSectionsι Z C.X₃).app U t = 0 :=
    (mem_supportedSectionsSubmodule_iff_exists_pow_smul_eq_zero C.X₃ hU a hZ _).mp t.property
  obtain ⟨s, hs, hst⟩ := exists_preimage_pow_smul_eq_zero a
    (Stacks.AlgebraicGeometry.QcohLimits.appₗ C.f U)
    (Stacks.AlgebraicGeometry.QcohLimits.appₗ C.g U) hex hsurj hdvd _ ht
  exact ⟨⟨s, (mem_supportedSectionsSubmodule_iff_exists_pow_smul_eq_zero C.X₂ hU a hZ s).mpr hs⟩,
    Subtype.ext hst⟩

/-- **The induced morphism on sections supported over an effective Cartier divisor is an
epimorphism.** The affine charts of [Stacks, Tag 07ZU] give a basis of affine opens on which the
complement of the preimage of the divisor is a basic open, and over such a chart the Stacks
lifting argument applies. -/
private lemma epi_supportedSectionsObjMap_of_universally_shortExact {X S : Scheme.{u}}
    (f : X ⟶ S) (I : S.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (C : ShortComplex X.Modules) (hC₀ : C.ShortExact)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (C.map (Scheme.Modules.pullback (pullback.fst f g))).ShortExact) :
    Epi (supportedSectionsObjMap (f.base ⁻¹' (I.support : Set S)) C.g) := by
  refine epi_supportedSectionsObjMap_of_local_divisibility _ C
    {V : X.Opens | IsAffineOpen V ∧ ∃ (U : S.Opens) (_ : IsAffineOpen U) (_ : V ≤ f ⁻¹ᵁ U)
      (a : Γ(S, U)), S.basicOpen a = U ⊓ I.support.compl} ?_ ?_
  · rw [Opens.isBasis_iff_nbhd]
    intro W x hxW
    obtain ⟨U, hxU, -, a, -, ha⟩ :=
      Stacks.Divisors.exists_affineOpen_basicOpen_eq_inf_compl_support I hI ⊤ (f.base x)
        (Set.mem_univ _)
    obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ W ⊓ f ⁻¹ᵁ U.1 from ⟨hxW, hxU⟩)
    exact ⟨V, ⟨hV, U.1, U.2, hVW.trans inf_le_right, a, ha⟩, hxV, hVW.trans inf_le_left⟩
  · rintro V ⟨hV, U, hU, hVU, a, ha⟩
    obtain ⟨hex, hsurj⟩ := exact_and_surjective_app_of_shortExact C hC₀ V hV
    refine ⟨hV, f.appLE U V hVU a, ?_, hex, hsurj,
      fun n x y hxy => exists_eq_pow_smul_of_universally_shortExact f C hC hU hV hVU a n x y hxy⟩
    rw [Scheme.basicOpen_appLE, ha]
    ext z
    exact ⟨fun hz => ⟨hz.1, hz.2.2⟩, fun hz => ⟨hz.1, hVU hz.1, hz.2⟩⟩

/-! ### The short exact sequence of strict transforms -/

/-- **Stacks Project, Tag 080W.** A short exact sequence of quasi-coherent `𝒪_X`-modules which
remains short exact after every base change of the base scheme `S` has short exact strict
transforms along the blowup of `S` in any quasi-coherent ideal, with the three maps determined
by the quotient maps onto the strict transforms. -/
@[stacks 080W]
public theorem strictTransformSheaf_shortExact {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (C : ShortComplex X.Modules)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (C.map (Scheme.Modules.pullback (pullback.fst f g))).ShortExact) :
    let b := blowUpToBase I
    let E := exceptionalIdeal I
    let p := pullback.fst f b
    let F₁ := (Scheme.Modules.pullback p).obj C.X₁
    let F₂ := (Scheme.Modules.pullback p).obj C.X₂
    let F₃ := (Scheme.Modules.pullback p).obj C.X₃
    let q₁ : F₁ ⟶ Stacks.StrictTransform.sheaf f b E C.X₁ := Stacks.StrictTransform.π f b E C.X₁
    let q₂ : F₂ ⟶ Stacks.StrictTransform.sheaf f b E C.X₂ := Stacks.StrictTransform.π f b E C.X₂
    let q₃ : F₃ ⟶ Stacks.StrictTransform.sheaf f b E C.X₃ := Stacks.StrictTransform.π f b E C.X₃
    ∃ (f' : Stacks.StrictTransform.sheaf f b E C.X₁ ⟶ Stacks.StrictTransform.sheaf f b E C.X₂)
      (g' : Stacks.StrictTransform.sheaf f b E C.X₂ ⟶ Stacks.StrictTransform.sheaf f b E C.X₃)
      (w : f' ≫ g' = 0),
      (ShortComplex.mk f' g' w).ShortExact ∧
        (q₁ ≫ f' = (Scheme.Modules.pullback p).map C.f ≫ q₂) ∧
        (q₂ ≫ g' = (Scheme.Modules.pullback p).map C.g ≫ q₃) := by
  intro b E p _F₁ _F₂ _F₃ q₁ q₂ q₃
  let Z := Stacks.StrictTransform.exceptionalPreimage f b E
  let D : ShortComplex (Stacks.StrictTransform.baseChange f b).Modules :=
    C.map (Scheme.Modules.pullback p)
  have hD : D.ShortExact := hC b
  have : D.X₁.IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pullback p).obj C.X₁).IsQuasicoherent
  have : D.X₂.IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pullback p).obj C.X₂).IsQuasicoherent
  have : D.X₃.IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pullback p).obj C.X₃).IsQuasicoherent
  have hfac₁ : Scheme.Modules.supportedSectionsι Z D.X₁ ≫ D.f ≫ q₂ = 0 :=
    supportedSectionsι_comp_comp_cokernel_π Z D.f
  have hfac₂ : Scheme.Modules.supportedSectionsι Z D.X₂ ≫ D.g ≫ q₃ = 0 :=
    supportedSectionsι_comp_comp_cokernel_π Z D.g
  have hf' : q₁ ≫ cokernel.desc _ _ hfac₁ = D.f ≫ q₂ := cokernel.π_desc _ _ hfac₁
  have hg' : q₂ ≫ cokernel.desc _ _ hfac₂ = D.g ≫ q₃ := cokernel.π_desc _ _ hfac₂
  refine ⟨cokernel.desc _ _ hfac₁, cokernel.desc _ _ hfac₂, ?_, ?_, hf', hg'⟩
  · refine (cancel_epi q₁).1 ?_
    rw [comp_zero, ← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc,
      ← Category.assoc, D.zero, zero_comp]
  · have hmf : Mono D.f := hD.mono_f
    have hmg : Epi D.g := hD.epi_g
    have hepi : Epi (supportedSectionsObjMap Z D.g) :=
      epi_supportedSectionsObjMap_of_universally_shortExact (pullback.snd f b) E
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) D hD
        fun g => shortExact_map_pullback_baseChange f C hC b g
    have hq₃ : Epi q₃ := inferInstanceAs (Epi (cokernel.π _))
    exact { exact := exact_cokernel_supportedSections Z D hD.exact _ _ _ hf' hg'
            mono_f := mono_cokernel_desc_supportedSections Z D.f hfac₁
            epi_g := epi_of_epi_fac hg' }

end AlgebraicGeometry

end
