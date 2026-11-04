module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedGlobalSections

/-!
# Short exactness of strict transforms on an algebraic space

In the situation of Stacks 0862 — a morphism `b : A' ⟶ A` of algebraic spaces over `S` together
with a subspace `E ⊆ A'`, and an algebraic space `f : X ⟶ A` over `A` — let
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a sequence of `𝒪_X`-modules which stays short exact after every base
change `Y ⟶ A`.  Stacks 0869 asserts that the strict transforms `Fᵢ'` of the `Fᵢ` then form a
short exact sequence `0 ⟶ F₁' ⟶ F₂' ⟶ F₃' ⟶ 0`.

The strict transform of a module is the quotient of its pullback to `X ×_A A'` by the subsheaf of
sections supported on the exceptional preimage `|pr_{A'}^{-1}E|`, so the two maps of the
candidate sequence come from functoriality of the cokernel, and the three assertions
`Mono`, `Exact`, `Epi` are three separate questions about that quotient.  Two of them are
settled here unconditionally.  The third is not, and is reduced to a single named statement.

## Main results

* `AlgebraicGeometry.Space.exists_strictTransformSheaf_shortComplex` is the tagged result: the
  strict transforms form a short complex whose two maps are pinned down by the quotient maps onto
  the strict transforms, the left-hand map is a monomorphism, the right-hand map is an
  epimorphism, and exactness in the middle holds **if and only if** the morphism induced on the
  subsheaves of sections supported on the exceptional preimage is an epimorphism.
* `AlgebraicGeometry.Space.exact_supportedQuotientShortComplex_iff` is that equivalence, for an
  arbitrary algebraic space, an arbitrary subset of its points and an arbitrary short exact
  sequence of modules on it; `AlgebraicGeometry.Space.mono_supportedQuotientMapLeft` and
  `AlgebraicGeometry.Space.epi_supportedQuotientMapRight` are the two unconditional halves at the
  same generality.
* `AlgebraicGeometry.Space.supportedSectionsMap` is the morphism a morphism of modules induces on
  the subsheaves of sections supported on a fixed subset of the points, and
  `AlgebraicGeometry.Space.supportedSectionsMap_comp_ι` is the equation pinning it down.
* `AlgebraicGeometry.Space.sectionSupportedIn_map` and
  `AlgebraicGeometry.Space.sectionSupportedIn_of_map` are the two halves of the behaviour of the
  support condition of Stacks 0859 under a morphism: a morphism never enlarges the support of a
  section, and a morphism injective on sections over every chart never shrinks it either.

## Implementation notes

Nothing here is specific to a blowup, or even to the exceptional preimage: the whole argument is
about the quotient of a module by its subsheaf of sections supported on a fixed subset `T` of the
points, so it is carried out at that generality and specialized at the end, exactly as
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransform.lean` carries out Stacks 0862 for an
arbitrary pair `(b, E)`.

Monomorphy of the left-hand map is the only one of the three assertions that needs anything about
sections.  It is the statement that a section of `pr_X^*F₁` whose image in `pr_X^*F₂` is supported
on `T` is itself supported on `T`, which is `sectionSupportedIn_of_map` applied to the injectivity
of `pr_X^*F₁ ⟶ pr_X^*F₂` on sections over every chart,
`SheafOfModules.injective_f_val_app_of_shortExact`.  Epimorphy of the right-hand map is formal.

The two diagram chases are done in an arbitrary abelian category, with every object and morphism
an opaque local hypothesis, and only then applied to `AlgebraicGeometry.Space.Modules`; carried
out directly on the sheaves they exceed the heartbeat ceiling at `whnf`, the cokernels of the
small étale site not being cheap to unfold.  The direction from epimorphy of the induced map on
supported sections to exactness is the argument of the scheme-level Stacks 080W,
`AlgebraicGeometry.strictTransformSheaf_shortExact`.  The converse is the chase that the nine
lemma packages, carried out with pullbacks rather than pseudo-elements: see the docstring of
`AlgebraicGeometry.Space.epi_of_exact_mk`.

The universal short exactness is carried as the source carries it, as a hypothesis quantified
over all cartesian squares over `A`; only its instance at `b` itself is used, so the lemmas it is
reduced to are stated with the short exactness of the single pullback `pr_X^*` instead.

## What is not done here

**Exactness in the middle is not proved, and it is the heart of Stacks 0869.**  What is proved
instead is that it is *equivalent* to epimorphy of the morphism
`AlgebraicGeometry.Space.supportedSectionsMap` induced on the subsheaves of sections supported on
the exceptional preimage.  Because that is an equivalence, granting it as a hypothesis would be
granting the conclusion, which is why no such hypothesis appears below and why the tag string
says `partial`.

The input that would discharge it is the one Stacks 0863 parts (2) and (3) supply: the
compatibility of the strict transform of a module with restriction to an étale chart, which
carries the scheme-level Stacks 080W across to algebraic spaces.  Part (1) of Stacks 0863 is
available, `AlgebraicGeometry.Space.isEtale_baseChange_blowup_of_isEtale`; parts (2) and (3) are
not, and `StacksFrontier/AlgebraicGeometry/Spaces/BlowupEtaleLocalization.lean` records that in its
own "What is not proved".  The three proved lemmas of the same section of the source — Stacks
0865, 0866 and 0868, in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean` — are conditional on
hypotheses named `hloc` for precisely that reason.

Attacking the reduced statement directly, rather than transporting Stacks 080W, is no longer
blocked by Stacks 0859: parts (2) and (3) of that tag, which earlier records of this development
list as missing, *are* now available in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartBasicOpenLocalization.lean`
(`AlgebraicGeometry.Space.sectionSupportedIn_iff_exists_pow_le_annihilator` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_supportedSectionsSubmodule`).  Three further
inputs are still wanting, and none of them is a statement about the sequence, so each would be a
legitimately weaker hypothesis than the conclusion: that the sections of a short exact sequence of
quasi-coherent modules are right exact over an affine étale chart, which this library carries as a
hypothesis wherever it is needed (see
`StacksFrontier/AlgebraicGeometry/Spaces/ShortExactQuasicoherent.lean`); that the exceptional
preimage is cut out on an affine étale chart by a *single* function, which is the effective
Cartier divisor structure of the exceptional divisor and is unavailable because Stacks 085Q
constructs no blowup of an algebraic space; and the divisibility step of the source's argument,
which reads the universal short exactness on the closed subspace cut out by a power of that
function and needs a comparison of the sections of a pullback module with an extension of scalars
that the chart machinery of this library does not yet provide.

No quasi-coherence hypothesis is carried on the modules: nothing proved here uses it.  Stacks 0869
states its sequence for quasi-coherent modules, and quasi-coherence is one of the inputs the
missing middle-exactness argument would consume.

## References

* [Stacks Project, Tag 0869](https://stacks.math.columbia.edu/tag/0869)
* [Stacks Project, Tag 0862](https://stacks.math.columbia.edu/tag/0862)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 080W](https://stacks.math.columbia.edu/tag/080W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry.Space

/-! ### Quotients by a chain of subobjects in an abelian category -/

section AbelianAux

variable {𝒜 : Type w} [Category.{v} 𝒜] [Abelian 𝒜] (C : ShortComplex 𝒜)
  {N₁ N₂ N₃ : 𝒜} (ι₁ : N₁ ⟶ C.X₁) (ι₂ : N₂ ⟶ C.X₂) (ι₃ : N₃ ⟶ C.X₃)

/-- The inclusion of a subobject is the kernel of the projection onto the quotient. -/
private theorem exact_mk_ι_cokernelπ {N M : 𝒜} (ι : N ⟶ M) [Mono ι] :
    (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).Exact :=
  ShortComplex.exact_of_f_is_kernel _
    (Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _))

/-- **Monomorphy of the induced map of quotients.**  The map induced on the quotients is a
monomorphism as soon as every morphism into `C.X₁` whose image in `C.X₂/N₂` vanishes factors
through `N₁`. -/
private theorem mono_of_forall_exists_lift [Mono ι₁] (f' : cokernel ι₁ ⟶ cokernel ι₂)
    (hf' : cokernel.π ι₁ ≫ f' = C.f ≫ cokernel.π ι₂)
    (hlift : ∀ {A : 𝒜} (k : A ⟶ C.X₁), k ≫ C.f ≫ cokernel.π ι₂ = 0 →
      ∃ l : A ⟶ N₁, l ≫ ι₁ = k) :
    Mono f' := by
  have w₁ : ι₁ ≫ C.f ≫ cokernel.π ι₂ = 0 := by
    rw [← hf', ← Category.assoc, cokernel.condition, zero_comp]
  have hLexact : (ShortComplex.mk ι₁ (C.f ≫ cokernel.π ι₂) w₁).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun k hk =>
      ⟨(hlift k hk).choose, (hlift k hk).choose_spec⟩)
  have heq : f' = cokernel.desc ι₁ (C.f ≫ cokernel.π ι₂) w₁ :=
    (cancel_epi (cokernel.π ι₁)).1 (hf'.trans (cokernel.π_desc _ _ w₁).symm)
  rw [heq]
  exact hLexact.mono_cokernelDesc

/-- **Exactness of the sequence of quotients, given epimorphy of the induced map of
subobjects.** -/
private theorem exact_mk_of_epi (hC : C.ShortExact)
    (f' : cokernel ι₁ ⟶ cokernel ι₂) (g' : cokernel ι₂ ⟶ cokernel ι₃)
    (hf' : cokernel.π ι₁ ≫ f' = C.f ≫ cokernel.π ι₂)
    (hg' : cokernel.π ι₂ ≫ g' = C.g ≫ cokernel.π ι₃)
    (u : N₂ ⟶ N₃) (hu : u ≫ ι₃ = ι₂ ≫ C.g) (hepiu : Epi u) (w : f' ≫ g' = 0) :
    (ShortComplex.mk f' g' w).Exact := by
  have hepig : Epi C.g := hC.epi_g
  have hepir : Epi g' := epi_of_epi_fac hg'
  refine ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ' _ _ ?_)
  intro A k hk
  have hpre : C.f ≫ (cokernel.π ι₂ ≫ k) = 0 := by
    rw [← Category.assoc, ← hf', Category.assoc, hk, comp_zero]
  have ha : C.g ≫ hC.exact.desc (cokernel.π ι₂ ≫ k) hpre = cokernel.π ι₂ ≫ k :=
    hC.exact.g_desc _ _
  have hTa : ι₃ ≫ hC.exact.desc (cokernel.π ι₂ ≫ k) hpre = 0 := by
    refine (cancel_epi u).mp ?_
    rw [← Category.assoc, hu, Category.assoc, ha, ← Category.assoc, cokernel.condition,
      zero_comp, comp_zero]
  refine ⟨cokernel.desc _ _ hTa, ?_⟩
  refine (cancel_epi (cokernel.π ι₂)).mp ?_
  rw [← Category.assoc, hg', Category.assoc, cokernel.π_desc, ha]

/-- **Conversely, exactness of the sequence of quotients forces the induced map of subobjects to
be an epimorphism.**

This is the diagram chase that the nine lemma packages, carried out with pullbacks.  Pull `ι₃`
back along the epimorphism `C.g` to get an epimorphism `pr₂ : P ⟶ N₃`; the composite
`P ⟶ C.X₂ ⟶ C.X₂/N₂` kills `g'`, so exactness factors it through `C.X₁/N₁`, and pulling that
factorisation back along `cokernel.π ι₁` gives an epimorphism `e : Q ⟶ P` together with
`q : Q ⟶ C.X₁`.  The difference of `e ≫ pr₁` and `q ≫ C.f` dies in `C.X₂/N₂`, hence factors
through `N₂` by a map `r`, and `r ≫ u` agrees with the epimorphism `e ≫ pr₂` after the
monomorphism `ι₃`. -/
private theorem epi_of_exact_mk (hC : C.ShortExact) [Mono ι₂] [Mono ι₃]
    (f' : cokernel ι₁ ⟶ cokernel ι₂) (g' : cokernel ι₂ ⟶ cokernel ι₃)
    (hf' : cokernel.π ι₁ ≫ f' = C.f ≫ cokernel.π ι₂)
    (hg' : cokernel.π ι₂ ≫ g' = C.g ≫ cokernel.π ι₃)
    (u : N₂ ⟶ N₃) (hu : u ≫ ι₃ = ι₂ ≫ C.g) (w : f' ≫ g' = 0) (hmono : Mono f')
    (hex : (ShortComplex.mk f' g' w).Exact) :
    Epi u := by
  have hepig : Epi C.g := hC.epi_g
  obtain ⟨P, pr₁, pr₂, hpr, hepi₂⟩ : ∃ (P : 𝒜) (pr₁ : P ⟶ C.X₂) (pr₂ : P ⟶ N₃),
      pr₁ ≫ C.g = pr₂ ≫ ι₃ ∧ Epi pr₂ :=
    ⟨pullback C.g ι₃, pullback.fst _ _, pullback.snd _ _, pullback.condition, inferInstance⟩
  have hv : (pr₁ ≫ cokernel.π ι₂) ≫ g' = 0 := by
    rw [Category.assoc, hg', ← Category.assoc, hpr, Category.assoc, cokernel.condition,
      comp_zero]
  obtain ⟨l, hl⟩ : ∃ l : P ⟶ cokernel ι₁, l ≫ f' = pr₁ ≫ cokernel.π ι₂ :=
    ⟨hex.lift _ hv, hex.lift_f _ hv⟩
  obtain ⟨Q, q, e, hq, hepie⟩ : ∃ (Q : 𝒜) (q : Q ⟶ C.X₁) (e : Q ⟶ P),
      q ≫ cokernel.π ι₁ = e ≫ l ∧ Epi e :=
    ⟨pullback (cokernel.π ι₁) l, pullback.fst _ _, pullback.snd _ _, pullback.condition,
      inferInstance⟩
  have h1 : (q ≫ C.f) ≫ cokernel.π ι₂ = e ≫ (pr₁ ≫ cokernel.π ι₂) := by
    rw [Category.assoc, ← hf', reassoc_of% hq, hl]
  have hm : (e ≫ pr₁ - q ≫ C.f) ≫ cokernel.π ι₂ = 0 := by
    rw [Preadditive.sub_comp, h1, Category.assoc, sub_self]
  obtain ⟨r, hr⟩ : ∃ r : Q ⟶ N₂, r ≫ ι₂ = e ≫ pr₁ - q ≫ C.f :=
    ⟨(exact_mk_ι_cokernelπ ι₂).lift _ hm, (exact_mk_ι_cokernelπ ι₂).lift_f _ hm⟩
  have hfinal : r ≫ u = e ≫ pr₂ := by
    refine (cancel_mono ι₃).1 ?_
    rw [Category.assoc, hu, ← Category.assoc, hr, Preadditive.sub_comp, Category.assoc,
      Category.assoc, C.zero, comp_zero, sub_zero, hpr, ← Category.assoc]
  exact epi_of_epi_fac hfinal

end AbelianAux

/-! ### Supports and morphisms -/

section Supported

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (T : Set (points B S hS F))

/-- A morphism does not enlarge the support of a section, so it carries sections supported on
`T` to sections supported on `T`. -/
theorem sectionSupportedIn_map {G H : Modules.{u, u} B S hS F hF} (φ : G ⟶ H)
    (W : SmallEtale B S hS F) (s : G.val.obj (op W))
    (hs : SectionSupportedIn B S hS F hF T G W s) :
    SectionSupportedIn B S hS F hF T H W (φ.val.app (op W) s) :=
  fun _ hx => hs (supportOfSection_map_subset B S hS F
    ((SheafOfModules.toSheaf _).map φ) W s hx)

/-- A morphism that is injective on sections over every chart does not shrink the support of a
section either, so being supported on `T` is reflected by it. -/
theorem sectionSupportedIn_of_map {G H : Modules.{u, u} B S hS F hF} (φ : G ⟶ H)
    (hinj : ∀ V : SmallEtale B S hS F, Function.Injective (φ.val.app (op V)))
    (W : SmallEtale B S hS F) (s : G.val.obj (op W))
    (h : SectionSupportedIn B S hS F hF T H W (φ.val.app (op W) s)) :
    SectionSupportedIn B S hS F hF T G W s := by
  refine fun x hx => h ?_
  refine Set.compl_subset_compl.mpr ?_ hx
  rintro y ⟨V, g, hzero, z, hz⟩
  refine ⟨V, g, ?_, z, hz⟩
  exact hinj V ((PresheafOfModules.naturality_apply φ.val g.op s).trans
    (hzero.trans (map_zero _).symm))

end Supported

/-! ### The quotient of a module by its sections supported on a subset -/

section Quotient

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} (T : Set (points B S hS X.1))

/-- The left-hand map of the short exact sequence of a submodule and its quotient is the
inclusion of the submodule, hence a monomorphism; instance search does not see through the
projection, so this is recorded for use as a local instance. -/
theorem mono_submoduleQuotientShortComplex_f (G : Modules.{u, u} B S hS X.1 X.2)
    (N : G.Submodule) : Mono (submoduleQuotientShortComplex B S hS X G N).f :=
  inferInstanceAs (Mono N.ι)

attribute [local instance] mono_submoduleQuotientShortComplex_f

/-- A section dies in the quotient by a submodule exactly when it lies in the submodule. -/
theorem cokernelπ_val_app_eq_zero_iff_mem (G : Modules.{u, u} B S hS X.1 X.2)
    (N : G.Submodule) (W : (SmallEtale B S hS X.1)ᵒᵖ) (x : G.val.obj W) :
    (cokernel.π N.ι).val.app W x = 0 ↔ x ∈ N.toSubmodule.obj W := by
  refine (SheafOfModules.exact_val_app_of_shortExact
    (shortExact_submoduleQuotientShortComplex B S hS X G N) W x).trans
    ⟨?_, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rintro ⟨y, rfl⟩
  exact y.property

/-- A section dies in the quotient by the supported sections exactly when it is supported on `T`. -/
private theorem cokernelπ_supported_val_app_eq_zero_iff
    (G : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS X.1)ᵒᵖ) (x : G.val.obj W) :
    (cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T G).ι).val.app W x = 0 ↔
      SectionSupportedIn B S hS X.1 X.2 T G W.unop x :=
  (cokernelπ_val_app_eq_zero_iff_mem G _ W x).trans
    (mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 T G W.unop x)

/-- A morphism carries the sections supported on `T` into the sections supported on `T`, so the
composite with the projection onto the quotient of the target vanishes. -/
theorem supportedSectionsι_comp_cokernelπ_eq_zero
    {G H : Modules.{u, u} B S hS X.1 X.2} (φ : G ⟶ H) :
    (supportedSectionsSubmodule B S hS X.1 X.2 T G).ι ≫ φ ≫
      cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T H).ι = 0 := by
  ext W x
  exact (cokernelπ_supported_val_app_eq_zero_iff T H W _).mpr
    (sectionSupportedIn_map T φ W.unop _
      ((mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 T G W.unop _).mp x.property))

/-- **The morphism induced on the subsheaves of sections supported on `T`.**  It is the unique
morphism compatible with the two inclusions, the inclusion of the supported sections of the
target being the kernel of the projection onto the quotient. -/
def supportedSectionsMap {G H : Modules.{u, u} B S hS X.1 X.2} (φ : G ⟶ H) :
    (supportedSectionsSubmodule B S hS X.1 X.2 T G).toSheafOfModules ⟶
      (supportedSectionsSubmodule B S hS X.1 X.2 T H).toSheafOfModules :=
  (shortExact_submoduleQuotientShortComplex B S hS X H
      (supportedSectionsSubmodule B S hS X.1 X.2 T H)).exact.lift
    ((supportedSectionsSubmodule B S hS X.1 X.2 T G).ι ≫ φ)
    ((Category.assoc _ _ _).trans (supportedSectionsι_comp_cokernelπ_eq_zero T φ))

/-- The induced morphism on supported sections commutes with the two inclusions. -/
@[reassoc]
theorem supportedSectionsMap_comp_ι {G H : Modules.{u, u} B S hS X.1 X.2} (φ : G ⟶ H) :
    supportedSectionsMap T φ ≫ (supportedSectionsSubmodule B S hS X.1 X.2 T H).ι =
      (supportedSectionsSubmodule B S hS X.1 X.2 T G).ι ≫ φ :=
  (shortExact_submoduleQuotientShortComplex B S hS X H
      (supportedSectionsSubmodule B S hS X.1 X.2 T H)).exact.lift_f _ _

variable (D : ShortComplex (Modules.{u, u} B S hS X.1 X.2))

/-- The morphism of quotients by the supported sections induced by the left-hand map of `D`. -/
def supportedQuotientMapLeft :
    cokernel (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₁).ι ⟶
      cokernel (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₂).ι :=
  cokernel.desc _ (D.f ≫ cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₂).ι)
    (supportedSectionsι_comp_cokernelπ_eq_zero T D.f)

/-- The morphism of quotients by the supported sections induced by the right-hand map of `D`. -/
def supportedQuotientMapRight :
    cokernel (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₂).ι ⟶
      cokernel (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₃).ι :=
  cokernel.desc _ (D.g ≫ cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₃).ι)
    (supportedSectionsι_comp_cokernelπ_eq_zero T D.g)

/-- The left-hand map of the quotient sequence is compatible with the projections onto the
quotients by the supported sections. -/
@[reassoc]
theorem cokernelπ_comp_supportedQuotientMapLeft :
    cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₁).ι ≫
        supportedQuotientMapLeft T D =
      D.f ≫ cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₂).ι :=
  cokernel.π_desc _ _ _

/-- The right-hand map of the quotient sequence is compatible with the projections onto the
quotients by the supported sections. -/
@[reassoc]
theorem cokernelπ_comp_supportedQuotientMapRight :
    cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₂).ι ≫
        supportedQuotientMapRight T D =
      D.g ≫ cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₃).ι :=
  cokernel.π_desc _ _ _

/-- The composite of the two maps of the quotient sequence vanishes. -/
theorem supportedQuotientMapLeft_comp_right :
    supportedQuotientMapLeft T D ≫ supportedQuotientMapRight T D = 0 := by
  refine (cancel_epi (cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₁).ι)).1 ?_
  rw [comp_zero, ← Category.assoc, cokernelπ_comp_supportedQuotientMapLeft, Category.assoc,
    cokernelπ_comp_supportedQuotientMapRight, ← Category.assoc, D.zero, zero_comp]

/-- The short complex of quotients by the supported sections. -/
def supportedQuotientShortComplex : ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
  ShortComplex.mk (supportedQuotientMapLeft T D) (supportedQuotientMapRight T D)
    (supportedQuotientMapLeft_comp_right T D)

/-- A morphism into `D.X₁` whose image in the quotient of `D.X₂` vanishes factors through the
sections of `D.X₁` supported on `T`: its sections land in the sections of `D.X₂` supported on
`T`, and being supported on `T` is reflected by the monomorphism `D.f`. -/
theorem exists_lift_of_comp_cokernelπ_eq_zero (hD : D.ShortExact)
    {A : Modules.{u, u} B S hS X.1 X.2} (k : A ⟶ D.X₁)
    (hk : k ≫ D.f ≫ cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₂).ι = 0) :
    ∃ l : A ⟶ (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₁).toSheafOfModules,
      l ≫ (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₁).ι = k := by
  have hinj : ∀ V : SmallEtale B S hS X.1, Function.Injective (D.f.val.app (op V)) :=
    fun V => SheafOfModules.injective_f_val_app_of_shortExact hD (op V)
  have hk1 : k ≫ cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₁).ι = 0 := by
    ext W a
    have hka : (cokernel.π (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₂).ι).val.app W
        (D.f.val.app W (k.val.app W a)) = 0 :=
      congrArg (fun m : A ⟶ _ => m.val.app W a) hk
    exact (cokernelπ_supported_val_app_eq_zero_iff T D.X₁ W _).mpr
      (sectionSupportedIn_of_map T D.f hinj W.unop _
        ((cokernelπ_supported_val_app_eq_zero_iff T D.X₂ W _).mp hka))
  exact ⟨_, (shortExact_submoduleQuotientShortComplex B S hS X D.X₁
    (supportedSectionsSubmodule B S hS X.1 X.2 T D.X₁)).exact.lift_f k hk1⟩

/-- **The left-hand map of the quotient sequence is a monomorphism.** -/
theorem mono_supportedQuotientMapLeft (hD : D.ShortExact) :
    Mono (supportedQuotientMapLeft T D) :=
  mono_of_forall_exists_lift D _ _ _ (cokernelπ_comp_supportedQuotientMapLeft T D)
    fun k hk => exists_lift_of_comp_cokernelπ_eq_zero T D hD k hk

/-- **The right-hand map of the quotient sequence is an epimorphism.** -/
theorem epi_supportedQuotientMapRight (hD : D.ShortExact) :
    Epi (supportedQuotientMapRight T D) :=
  have : Epi D.g := hD.epi_g
  epi_of_epi_fac (cokernelπ_comp_supportedQuotientMapRight T D)

/-- **Exactness in the middle of the quotient sequence, given epimorphy of the induced map on
supported sections.** -/
theorem exact_supportedQuotientShortComplex_of_epi (hD : D.ShortExact)
    (hepi : Epi (supportedSectionsMap T D.g)) :
    (supportedQuotientShortComplex T D).Exact :=
  exact_mk_of_epi D _ _ _ hD _ _ (cokernelπ_comp_supportedQuotientMapLeft T D)
    (cokernelπ_comp_supportedQuotientMapRight T D) (supportedSectionsMap T D.g)
    (supportedSectionsMap_comp_ι T D.g) hepi (supportedQuotientMapLeft_comp_right T D)

/-- **Conversely, exactness in the middle of the quotient sequence forces the induced map on
supported sections to be an epimorphism.** -/
theorem epi_supportedSectionsMap_of_exact (hD : D.ShortExact)
    (hex : (supportedQuotientShortComplex T D).Exact) :
    Epi (supportedSectionsMap T D.g) :=
  epi_of_exact_mk D _ _ _ hD _ _ (cokernelπ_comp_supportedQuotientMapLeft T D)
    (cokernelπ_comp_supportedQuotientMapRight T D) (supportedSectionsMap T D.g)
    (supportedSectionsMap_comp_ι T D.g) (supportedQuotientMapLeft_comp_right T D)
    (mono_supportedQuotientMapLeft T D hD) hex

/-- **Exactness in the middle of the quotient sequence is equivalent to epimorphy of the induced
map on the supported sections.** -/
theorem exact_supportedQuotientShortComplex_iff (hD : D.ShortExact) :
    (supportedQuotientShortComplex T D).Exact ↔ Epi (supportedSectionsMap T D.g) :=
  ⟨epi_supportedSectionsMap_of_exact T D hD, exact_supportedQuotientShortComplex_of_epi T D hD⟩

end Quotient

/-! ### The sequence of strict transforms -/

section StrictTransform

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)

/-- The pullback to `X ×_A A'` of a short complex of `𝒪_X`-modules. -/
abbrev strictTransformPullbackShortComplex
    (C : ShortComplex (Modules.{u, u} B S hS X.1 X.2)) :
    ShortComplex (Modules.{u, u} B S hS (strictTransformPullback B S hS f b).1
      (strictTransformPullback B S hS f b).2) :=
  C.map (modulePullback B S hS (strictTransformPullbackToSource B S hS f b))

variable (E : Subfunctor A'.1) (C : ShortComplex (Modules.{u, u} B S hS X.1 X.2))

/-- The left-hand map of the sequence of strict transforms, induced by `F₁ ⟶ F₂`. -/
def strictTransformSheafMapLeft :
    strictTransformSheaf B S hS f b E C.X₁ ⟶ strictTransformSheaf B S hS f b E C.X₂ :=
  supportedQuotientMapLeft (exceptionalPreimageSet B S hS f b E)
    (strictTransformPullbackShortComplex B S hS f b C)

/-- The right-hand map of the sequence of strict transforms, induced by `F₂ ⟶ F₃`. -/
def strictTransformSheafMapRight :
    strictTransformSheaf B S hS f b E C.X₂ ⟶ strictTransformSheaf B S hS f b E C.X₃ :=
  supportedQuotientMapRight (exceptionalPreimageSet B S hS f b E)
    (strictTransformPullbackShortComplex B S hS f b C)

/-- The left-hand map of the sequence of strict transforms is compatible with the quotient maps
onto the strict transforms. -/
theorem strictTransformSheafQuotient_comp_mapLeft :
    strictTransformSheafQuotient B S hS f b E C.X₁ ≫ strictTransformSheafMapLeft B S hS f b E C =
      (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.f ≫
        strictTransformSheafQuotient B S hS f b E C.X₂ :=
  cokernelπ_comp_supportedQuotientMapLeft (exceptionalPreimageSet B S hS f b E)
    (strictTransformPullbackShortComplex B S hS f b C)

/-- The right-hand map of the sequence of strict transforms is compatible with the quotient maps
onto the strict transforms. -/
theorem strictTransformSheafQuotient_comp_mapRight :
    strictTransformSheafQuotient B S hS f b E C.X₂ ≫ strictTransformSheafMapRight B S hS f b E C =
      (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.g ≫
        strictTransformSheafQuotient B S hS f b E C.X₃ :=
  cokernelπ_comp_supportedQuotientMapRight (exceptionalPreimageSet B S hS f b E)
    (strictTransformPullbackShortComplex B S hS f b C)

/-- The composite of the two maps of the sequence of strict transforms vanishes. -/
theorem strictTransformSheafMapLeft_comp_mapRight :
    strictTransformSheafMapLeft B S hS f b E C ≫ strictTransformSheafMapRight B S hS f b E C =
      0 :=
  supportedQuotientMapLeft_comp_right (exceptionalPreimageSet B S hS f b E)
    (strictTransformPullbackShortComplex B S hS f b C)

/-- **Stacks 0869, as far as this library reaches it.**  In the situation of Stacks 0862, let
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a sequence of `𝒪_X`-modules which is short exact after every base
change `Y ⟶ A`.  Then the strict transforms of the `Fᵢ` relative to `(b, E)` form a short
complex whose two maps are determined by the quotient maps onto the strict transforms; the
left-hand map is a monomorphism and the right-hand map is an epimorphism, and exactness in the
middle is equivalent to epimorphy of the morphism induced on the subsheaves of sections
supported on the exceptional preimage.

Everything asserted here is unconditional.  Exactness in the middle — the heart of the tag — is
*not* proved; the last conjunct is the exact reduction of it, and the module documentation
records what would discharge the reduced statement and why that input is absent. -/
@[stacks 0869 "partial: the short complex of strict transforms with its two maps pinned down by \
the quotient maps, monomorphic on the left and epimorphic on the right, all unconditional; \
exactness in the middle is NOT proved and is instead reduced, as an equivalence, to epimorphy \
of the induced map on the subsheaves of sections supported on the exceptional preimage — the \
statement that Stacks 0863 parts (2) and (3) together with the scheme-level Stacks 080W would \
supply and that this library cannot reach"]
theorem exists_strictTransformSheaf_shortComplex
    (hC : ∀ (Y P : AlgebraicSpaces B S hS) (t : Y ⟶ A) (pX : P ⟶ X) (pY : P ⟶ Y),
      IsPullback pX pY f t → (C.map (modulePullback B S hS pX)).ShortExact) :
    ∃ (f' : strictTransformSheaf B S hS f b E C.X₁ ⟶ strictTransformSheaf B S hS f b E C.X₂)
      (g' : strictTransformSheaf B S hS f b E C.X₂ ⟶ strictTransformSheaf B S hS f b E C.X₃)
      (w : f' ≫ g' = 0),
      Mono f' ∧ Epi g' ∧
      (strictTransformSheafQuotient B S hS f b E C.X₁ ≫ f' =
        (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.f ≫
          strictTransformSheafQuotient B S hS f b E C.X₂) ∧
      (strictTransformSheafQuotient B S hS f b E C.X₂ ≫ g' =
        (modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.g ≫
          strictTransformSheafQuotient B S hS f b E C.X₃) ∧
      ((ShortComplex.mk f' g' w).Exact ↔
        Epi (supportedSectionsMap (exceptionalPreimageSet B S hS f b E)
          ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.g))) := by
  have hD : (strictTransformPullbackShortComplex B S hS f b C).ShortExact :=
    hC A' (strictTransformPullback B S hS f b) b _ _
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
  exact ⟨strictTransformSheafMapLeft B S hS f b E C, strictTransformSheafMapRight B S hS f b E C,
    strictTransformSheafMapLeft_comp_mapRight B S hS f b E C,
    mono_supportedQuotientMapLeft _ _ hD, epi_supportedQuotientMapRight _ _ hD,
    strictTransformSheafQuotient_comp_mapLeft B S hS f b E C,
    strictTransformSheafQuotient_comp_mapRight B S hS f b E C,
    exact_supportedQuotientShortComplex_iff _ _ hD⟩

end StrictTransform

end AlgebraicGeometry.Space

end
