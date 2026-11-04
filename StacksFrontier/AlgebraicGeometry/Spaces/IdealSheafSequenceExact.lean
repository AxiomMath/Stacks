module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIntersectionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealSheafKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesRightExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsIdComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sequence of a chain of closed subspaces is exact in the middle

Let `Y, Z ⊆ X` be closed subspaces of an algebraic space `X` over a scheme `S` contained in a
big fppf site `B`, with `Z ⊆ Y`, write `j : Y ⟶ X` for the inclusion, and let `W ⊆ Y` be a closed
subspace sent into `Z` by `j`.  This file proves that the sequence of defining ideal sheaves

`(𝟙 X)^*𝓘_Y ⟶ 𝓘_Z ⟶ j_*𝓘_W`

is exact in the middle — the inclusion of defining ideal sheaves *is* the kernel of the
transpose of the map `j^*𝓘_Z ⟶ 𝓘_W` of [Stacks Project, Tag 04CP] — that for the inverse-image
square the transpose is an epimorphism, and that exactness in the middle survives the two
inverse images along `j` and along the inclusion of `W`.  It then identifies that sequence, at
the inverse-image square, with the conormal sequence of [Stacks Project, Tag 06BD] and concludes
**the exactness in the middle of that tag**, the one clause of it this development was missing.

## Main results

* `AlgebraicGeometry.Space.idealSheafMap_comp_homEquiv_idealSheafMap_eq_zero`: the sequence of
  defining ideal sheaves is a complex.
* `AlgebraicGeometry.Space.exact_idealSheafShortComplex`: **it is exact in the middle.** The
  inclusion `𝓘_Y ⊆ 𝓘_Z`, read as the map of [Stacks Project, Tag 04CP] at the square whose lower
  edge is the identity of `X`, is a kernel of the transpose `𝓘_Z ⟶ j_*𝓘_W`: the transpose
  followed by the direct image of `𝓘_W ⊆ 𝒪_Y`, a monomorphism, is the inclusion `𝓘_Z ⊆ 𝒪_X`
  followed by the structure projection `𝒪_X ⟶ j_*𝒪_Y`
  (`AlgebraicGeometry.Space.homEquiv_idealSheafMap_comp_pushforward_ι`), whose kernel is `𝓘_Y`
  (`AlgebraicGeometry.Space.definingIdealSheafIsoKernel`).
* `AlgebraicGeometry.Space.epi_homEquiv_idealSheafMap`: **the transpose is an epimorphism** as
  soon as the map of [Stacks Project, Tag 04CP] is, which at the inverse-image square it is by
  `AlgebraicGeometry.Space.epi_idealSheafMap`.  The unit of the adjunction of [Stacks Project,
  Tag 03D7] is an epimorphism at every module, by the essential-image clause of [Stacks Project,
  Tag 04CJ], part (3), and the direct image along a closed immersion preserves epimorphisms.
* `AlgebraicGeometry.Space.exact_map_idealSheafSequence`: **the sequence stays exact in the
  middle after the two inverse images**, the last term becoming `𝓘_W` by the counit isomorphism
  of [Stacks Project, Tag 04CJ], part (2); and
  `AlgebraicGeometry.Space.exact_mk_map_idealSheafSequence`, the same with the short complex
  spelled by its two morphisms.
* `AlgebraicGeometry.Space.conormalSequence_comparison_square₁₂` and
  `AlgebraicGeometry.Space.conormalSequence_comparison_square₂₃`: **the two squares identifying
  that sequence with the conormal sequence of the chain**, through the comparison isomorphisms
  of `AlgebraicGeometry.Space.conormalPullbackCompIso`.
* `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero_chain`: the two arrows of the
  conormal sequence of the chain compose to zero, for an arbitrary upper subspace.  Its instance
  at the inverse-image square is the clause
  `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero`.
* `AlgebraicGeometry.Space.exact_conormalShortComplex`: **exactness in the middle of [Stacks
  Project, Tag 06BD]**, the conormal sequence of a pair `Z ⊆ Y ⊆ X` of closed subspaces read at
  the inverse image of `Z` along the inclusion of `Y`.  Its companions, the vanishing of the
  composite and epimorphy of the second arrow, are
  `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero` and
  `AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces`, so the tag carries all three of
  its clauses.
* `CategoryTheory.Limits.exact_mk_of_squares`: exactness in the middle transported along three
  isomorphisms, with neither short complex passed as an argument.

## Implementation notes

**Why the statements are at a variable upper subspace.**  The configuration the file is used in
has `W` the inverse image of `Z` along `j`, but almost nothing in the argument uses that: only
epimorphy of the map of [Stacks Project, Tag 04CP] does, and it is carried as a hypothesis.  The
upper subspace, the vertical morphism and the commutativity of the square are taken as variables
and instantiated once, in `AlgebraicGeometry.Space.exact_map_idealSheafSequence`.  Keeping the
fibre-product spelling out of the statements is what makes the elaboration cheap: the same
statements written at the concrete inverse image exhaust the heartbeat budget.

**The two spellings of the inverse image along the projection, and why the final statement
names its objects.**  The inverse-image functor `AlgebraicGeometry.Space.modulePullback` carries
the source and target of its morphism as implicit arguments, and for the projection
`p : j⁻¹(Z) ⟶ Z` of the fibre-product square there are two spellings of them: the one the
variable `p` of the section below declares, whose source is the pair of projections of the
closed subspace `W`, and the one `AlgebraicGeometry.Space.preimageProjection` declares, whose
source is built from `CategoryTheory.Subfunctor.preimage` directly.  The two objects are
definitionally equal, and a type ascription crosses between them at no cost; but the elaborator
will *not* cross between them inside `CategoryTheory.Functor.map` — elaboration unfolds
`modulePullback` and exhausts the heartbeat budget.  So the statement of
`AlgebraicGeometry.Space.exact_conormalShortComplex` gives those two objects explicitly, in the
spelling the comparison squares use, and its vanishing is the instance of
`AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero_chain` rather than the
clause-one statement, which is written at the other one.  Both choices are invisible in what the
statement prints, and the statement is the same proposition either way.

**Why the abstract lemmas are abstract.**  Every step of the argument that is pure category
theory — that a morphism whose composite with a monomorphism is a kernel is itself a kernel, that
a kernel fork transports along an isomorphism of its point, that naturality can be read off a
factorisation, that exactness in the middle transports along three isomorphisms — is stated at
variable objects in a variable category and instantiated.  Stated at the sheaf categories of
this development the same steps do not survive the heartbeat budget; instantiating an abstract
statement costs nothing.  For the same reason
`CategoryTheory.Limits.exact_mk_of_squares` takes neither short complex as an argument: the
source complex is given by its two morphisms and the three comparison morphisms are implicit, so
that every hypothesis is read off the two commuting squares and nothing has to be matched
against a projection of a `CategoryTheory.ShortComplex`.

**Why monomorphy and epimorphy are explicit hypotheses.**  The abstract lemmas take `Mono`,
`Epi`, `IsIso` and `PreservesZeroMorphisms` as *explicit* arguments rather than instance
arguments.  Instance search for, say, `Mono (definingIdealSheaf B S hS X Z).ι` runs at reducible
transparency and fails at the spelling an abstract lemma's instantiation produces, while the
same fact is found by `inferInstance` in a goal that names the category directly; the statement
`AlgebraicGeometry.Space.mono_definingIdealSheaf_ι` is that `inferInstance`, made once at the
spelling of `AlgebraicGeometry.Space.Modules`, and then passed by hand, and
`AlgebraicGeometry.Space.mono_modulePushforward_map` and
`AlgebraicGeometry.Space.epi_modulePushforward_map` play the same role for the direct image.

## References

* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD), the conormal sequence of
  a chain of immersions.
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the map of defining
  ideal sheaves and of conormal modules of a commutative square.
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ), the counit and the
  essential image of the direct image along a closed immersion.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the inverse and direct
  images of modules and their unit laws.
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7), the adjunction.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal
  sheaf.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- A composite vanishes when it does so after a monomorphism. -/
theorem comp_eq_zero_of_mono_of_fac {A K Kw E P : C} (k : A ⟶ K) (g : K ⟶ Kw) (m : Kw ⟶ P)
    (hm : Mono m) (ιK : K ⟶ E) (π : E ⟶ P) (hgm : g ≫ m = ιK ≫ π) (a : A ⟶ E)
    (hk : k ≫ ιK = a) (ha : a ≫ π = 0) : k ≫ g = 0 := by
  have _ := hm
  refine (cancel_mono m).mp ?_
  rw [zero_comp, Category.assoc, hgm, ← Category.assoc, hk, ha]

/-- The composite of the two maps of the ideal-sheaf sequence vanishes. -/
theorem comp_eq_zero_of_natIsoId {F : C ⥤ C} (α : F ≅ 𝟭 C) {A O P K Kw Kr : C}
    (ιA : A ⟶ O) (π : O ⟶ P) (κ : Kr ⟶ O) (hκ0 : κ ≫ π = 0) (ρ : A ≅ Kr)
    (hρ : ρ.hom ≫ κ = ιA) (s : F.obj O ⟶ O) (hs : s = α.hom.app O) (k : F.obj A ⟶ K)
    (ιK : K ⟶ O) (hk : k ≫ ιK = F.map ιA ≫ s) (g : K ⟶ Kw) (m : Kw ⟶ P) (hm : Mono m)
    (hgm : g ≫ m = ιK ≫ π) : k ≫ g = 0 := by
  have hk' : k ≫ ιK = α.hom.app A ≫ ιA := by
    rw [hk, hs, α.hom.naturality ιA, Functor.id_map]
  have h0 : (α.hom.app A ≫ ιA) ≫ π = 0 := by
    rw [Category.assoc, ← hρ, Category.assoc, hκ0, comp_zero, comp_zero]
  exact comp_eq_zero_of_mono_of_fac k g m hm ιK π hgm _ hk' h0

/-- A morphism whose composite with a monomorphism is a kernel is itself a kernel. -/
def isLimit_kernelFork_of_mono_fac {A B K E F : C} (f : A ⟶ B) (g : B ⟶ K) (m : K ⟶ F)
    (b : B ⟶ E) (π : E ⟶ F) (h : A ⟶ E) (hf : Mono f) (hm : Mono m) (hb : Mono b)
    (hfb : f ≫ b = h) (hgm : g ≫ m = b ≫ π) (hπ : h ≫ π = 0)
    (hker : IsLimit (KernelFork.ofι h hπ)) (w : f ≫ g = 0) :
    IsLimit (KernelFork.ofι f w) := by
  have _ := hf
  have _ := hm
  have _ := hb
  have hcond : ∀ {T : C} (u : T ⟶ B), u ≫ g = 0 → (u ≫ b) ≫ π = 0 := by
    intro T u hu
    rw [Category.assoc, ← hgm, ← Category.assoc, hu, zero_comp]
  have hfac : ∀ {T : C} (u : T ⟶ B) (hu : u ≫ g = 0),
      (KernelFork.IsLimit.lift' hker (u ≫ b) (hcond u hu)).1 ≫ f = u := by
    intro T u hu
    refine (cancel_mono b).mp ?_
    rw [Category.assoc, hfb]
    exact (KernelFork.IsLimit.lift' hker (u ≫ b) (hcond u hu)).2
  exact KernelFork.IsLimit.ofι f w
    (fun u hu ↦ (KernelFork.IsLimit.lift' hker (u ≫ b) (hcond u hu)).1)
    (fun u hu ↦ hfac u hu)
    (fun u hu mm hmm ↦ (cancel_mono f).mp (hmm.trans (hfac u hu).symm))

/-- A kernel fork transported along an isomorphism of its point is a kernel fork. -/
def isLimit_kernelFork_of_iso {A Ar E P : C} (ιA : A ⟶ E) (π : E ⟶ P) (hπ : ιA ≫ π = 0)
    (κ : Ar ⟶ E) (hκ0 : κ ≫ π = 0) (hκ : IsLimit (KernelFork.ofι κ hκ0)) (ρ : A ≅ Ar)
    (hρ : ρ.hom ≫ κ = ιA) : IsLimit (KernelFork.ofι ιA hπ) :=
  IsLimit.ofIsoLimit hκ (Fork.ext ρ (by exact hρ)).symm

/-- **The kernel of a morphism read through an inverse image along an identity.**  Suppose given
a kernel `κ` of `π : E ⟶ P` presented through an isomorphism `ρ` as the object `A`, an
endofunctor `F` isomorphic to the identity by `α`, and a morphism `k : F.obj A ⟶ K` whose
composite with a monomorphism `ιK : K ⟶ E` is the inverse image of the kernel inclusion read
through `s : F.obj E ⟶ E`.  Then `k` is a kernel of any `g : K ⟶ Kw` whose composite with a
monomorphism `m : Kw ⟶ P` is `ιK ≫ π`. -/
def isLimit_kernelFork_of_natIsoId {F : C ⥤ C} (α : F ≅ 𝟭 C) {A O P K Kw Kr : C}
    (ιA : A ⟶ O) (π : O ⟶ P) (κ : Kr ⟶ O) (hκ0 : κ ≫ π = 0)
    (hκ : IsLimit (KernelFork.ofι κ hκ0)) (ρ : A ≅ Kr) (hρ : ρ.hom ≫ κ = ιA)
    (s : F.obj O ⟶ O) (hs : s = α.hom.app O) (k : F.obj A ⟶ K) (ιK : K ⟶ O) (hιK : Mono ιK)
    (hk : k ≫ ιK = F.map ιA ≫ s) (g : K ⟶ Kw) (m : Kw ⟶ P) (hm : Mono m)
    (hgm : g ≫ m = ιK ≫ π) (w : k ≫ g = 0) :
    IsLimit (KernelFork.ofι k w) := by
  have _ : Mono κ := mono_of_isLimit_fork hκ
  have hk' : k ≫ ιK = α.hom.app A ≫ ιA := by
    rw [hk, hs, α.hom.naturality ιA, Functor.id_map]
  have hmonoA : Mono ιA := by
    rw [← hρ]
    infer_instance
  have _ := hmonoA
  have h0 : (α.hom.app A ≫ ιA) ≫ π = 0 := by
    rw [Category.assoc, ← hρ, Category.assoc, hκ0, comp_zero, comp_zero]
  have hker : IsLimit (KernelFork.ofι (α.hom.app A ≫ ιA) h0) :=
    isLimit_kernelFork_of_iso _ π h0 κ hκ0 hκ (asIso (α.hom.app A) ≪≫ ρ) (by
      rw [Iso.trans_hom, asIso_hom, Category.assoc, hρ])
  exact isLimit_kernelFork_of_mono_fac k g m ιK π (α.hom.app A ≫ ιA)
    (mono_of_mono_fac hk') hm hιK hk' hgm h0 hker w

omit [HasZeroMorphisms C] in
/-- The forward morphism of an isomorphism is an isomorphism. -/
theorem isIso_hom_app {A Bd : C} (e : A ≅ Bd) : IsIso e.hom :=
  ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

omit [HasZeroMorphisms C] in
/-- The composite of two isomorphisms is an isomorphism. -/
theorem isIso_comp_of {A Bd K : C} (f : A ⟶ Bd) (g : Bd ⟶ K) (hf : IsIso f) (hg : IsIso g) :
    IsIso (f ≫ g) := by
  have _ := hf
  have _ := hg
  infer_instance

omit [HasZeroMorphisms C] in
/-- A functor carries an isomorphism to an isomorphism. -/
theorem isIso_map_of {D : Type*} [Category D] (F : C ⥤ D) {A Bd : C} (f : A ⟶ Bd)
    (hf : IsIso f) : IsIso (F.map f) := by
  have _ := hf
  infer_instance

/-- **Exactness in the middle transported along three isomorphisms.**  A short complex is exact
when another one is and the two are related componentwise by isomorphisms making both squares
commute. -/
theorem exact_of_components (S₁ : ShortComplex C) {S₂ : ShortComplex C} (h : S₂.Exact)
    (τ₁ : S₁.X₁ ⟶ S₂.X₁) (hτ₁ : IsIso τ₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂) (hτ₂ : IsIso τ₂)
    (τ₃ : S₁.X₃ ⟶ S₂.X₃) (hτ₃ : IsIso τ₃) (c12 : τ₁ ≫ S₂.f = S₁.f ≫ τ₂)
    (c23 : τ₂ ≫ S₂.g = S₁.g ≫ τ₃) : S₁.Exact :=
  have _ := hτ₁
  have _ := hτ₂
  have _ := hτ₃
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := S₁) (asIso τ₁) (asIso τ₂) (asIso τ₃) c12 c23).symm h

/-- **Exactness in the middle transported along three isomorphisms, read off the two squares.**
Neither short complex is an argument: the source complex is given by its two morphisms and the
three comparison morphisms are left implicit, so that every hypothesis is read off the two
commuting squares and nothing has to be matched against a projection of a `ShortComplex`. -/
theorem exact_mk_of_squares {A₁ A₂ A₃ Bd₁ Bd₂ Bd₃ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
    (w : f ≫ g = 0) {f' : Bd₁ ⟶ Bd₂} {g' : Bd₂ ⟶ Bd₃} {τ₁ : A₁ ⟶ Bd₁} {τ₂ : A₂ ⟶ Bd₂}
    {τ₃ : A₃ ⟶ Bd₃} (c12 : τ₁ ≫ f' = f ≫ τ₂) (c23 : τ₂ ≫ g' = g ≫ τ₃) (hτ₁ : IsIso τ₁)
    (hτ₂ : IsIso τ₂) (hτ₃ : IsIso τ₃) {w' : f' ≫ g' = 0}
    (h : (ShortComplex.mk f' g' w').Exact) : (ShortComplex.mk f g w).Exact :=
  have _ := hτ₁
  have _ := hτ₂
  have _ := hτ₃
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := ShortComplex.mk f g w) (S₂ := ShortComplex.mk f' g' w')
      (asIso τ₁) (asIso τ₂) (asIso τ₃) c12 c23).symm h

/-- Naturality of a transformation, read off a factorisation of one leg. -/
theorem comp_natTrans_app_eq_of_fac {D E : Type*} [Category D] [Category E] {F G : D ⥤ E}
    (α : F ⟶ G) {A Bd : D} (k : A ⟶ Bd) {A' : E} (c : A' ⟶ F.obj A) (φ : A' ⟶ F.obj Bd)
    (hφ : φ = c ≫ F.map k) : (c ≫ α.app A) ≫ G.map k = φ ≫ α.app Bd := by
  rw [hφ, Category.assoc, Category.assoc, α.naturality k]

/-- A composite whose second leg factors through the image of a vanishing composite
vanishes. -/
theorem comp_eq_zero_of_map_of_fac {D : Type*} [Category D] [HasZeroMorphisms D] (F : C ⥤ D)
    (hF : F.PreservesZeroMorphisms) {A Bd K : C} (k : A ⟶ Bd) (t : Bd ⟶ K) (hkt : k ≫ t = 0)
    {K' : D} (u : F.obj K ⟶ K') (a : F.obj Bd ⟶ K') (ha : F.map t ≫ u = a) :
    F.map k ≫ a = 0 := by
  have _ := hF
  rw [← ha, ← Category.assoc, ← F.map_comp, hkt, F.map_zero, zero_comp]

/-- A functor preserving zero morphisms carries a vanishing composite to a vanishing
composite. -/
theorem map_comp_eq_zero {D : Type*} [Category D] [HasZeroMorphisms D] (F : C ⥤ D)
    (hF : F.PreservesZeroMorphisms) {A Bd K : C} (a : A ⟶ Bd) (b : Bd ⟶ K) (h : a ≫ b = 0) :
    F.map a ≫ F.map b = 0 := by
  have _ := hF
  rw [← F.map_comp, h, F.map_zero]

omit [HasZeroMorphisms C] in
/-- The inverse image of a transpose along an adjunction, followed by the counit, is the
morphism transposed. -/
@[ega "0 3.5.3" "(v^b)^♯ = v", ega "0 3.5.4" "more general"]
theorem map_homEquiv_comp_counit {D : Type*} [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {A : C} {Bo : D} (f : F.obj A ⟶ Bo) :
    F.map (adj.homEquiv A Bo f) ≫ adj.counit.app Bo = f :=
  (Adjunction.homEquiv_counit adj A Bo (adj.homEquiv A Bo f)).symm.trans
    ((adj.homEquiv A Bo).symm_apply_apply f)

omit [HasZeroMorphisms C] in
/-- A transpose along an adjunction is an epimorphism when the unit is one and the right adjoint
carries the morphism to one. -/
theorem epi_homEquiv_of_epi {D : Type*} [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {A : C} {Bo : D} (f : F.obj A ⟶ Bo) (h1 : Epi (adj.unit.app A)) (h2 : Epi (G.map f)) :
    Epi (adj.homEquiv A Bo f) := by
  have _ := h1
  have _ := h2
  rw [Adjunction.homEquiv_unit]
  exact epi_comp _ _

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Monomorphy at the spelling of `AlgebraicGeometry.Space.Modules` -/

/-- The inclusion of a defining ideal sheaf into the structure sheaf is a monomorphism, at the
spelling of `AlgebraicGeometry.Space.Modules`. -/
theorem mono_definingIdealSheaf_ι (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) : Mono (definingIdealSheaf B S hS X Z).ι := inferInstance

/-! ### The ideal-sheaf sequence of a chain of closed subspaces -/

section Chain

variable {X : AlgebraicSpaces B S hS} (Y Z : ClosedSubspaces B S hS X.1) (hZY : Z.1 ≤ Y.1)
    (W : ClosedSubspaces B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS).1)
    (p : (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W ≫
        subspaceInclusion B S hS X Y =
      p ≫ subspaceInclusion B S hS X Z)

/-- The direct image of the inclusion of a defining ideal sheaf is a monomorphism. -/
private theorem mono_pushforward_ι :
    Mono ((modulePushforward B S hS (subspaceInclusion B S hS X Y)).map
      (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W).ι) :=
  mono_modulePushforward_map B S hS (subspaceInclusion B S hS X Y)
    (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W).ι
    (mono_definingIdealSheaf_ι B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W)

/-- The transpose of the map `j^*𝓘_Z ⟶ 𝓘_W`, pushed to `𝒪_Y`, is the inclusion of `𝓘_Z`
followed by the structure projection. -/
private theorem homEquiv_idealSheafMap_fac :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y)).homEquiv _ _
        (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq) ≫
      (modulePushforward B S hS (subspaceInclusion B S hS X Y)).map
        (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W).ι =
    (definingIdealSheaf B S hS X Z).ι ≫ structureProjection B S hS X Y :=
  (homEquiv_idealSheafMap_comp_pushforward_ι B S hS W Z
        (subspaceInclusion B S hS X Y) p hsq).trans
      (congrArg (fun z ↦ (definingIdealSheaf B S hS X Z).ι ≫ z)
        (structureProjection_eq_structureProjectionOfHom B S hS X Y).symm)

/-- The transpose along the adjunction of [Stacks Project, Tag 03D7] of the map `j^*𝓘_Z ⟶ 𝓘_W`
of [Stacks Project, Tag 04CP], composed with the inclusion `𝓘_Y ⊆ 𝓘_Z` read as the map of
[Stacks Project, Tag 04CP] of the square with lower edge the identity of `X`, vanishes. -/
theorem idealSheafMap_comp_homEquiv_idealSheafMap_eq_zero :
    idealSheafMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
          (subspaceInclusion_homOfLe_square B S hS Y Z hZY) ≫
        (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y)).homEquiv _ _
          (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq) = 0 :=
  comp_eq_zero_of_natIsoId (modulePullbackIdIso B S hS X)
    (definingIdealSheaf B S hS X Y).ι (structureProjection B S hS X Y)
    (kernel.ι (structureProjection B S hS X Y))
    (kernel.condition (structureProjection B S hS X Y))
    (definingIdealSheafIsoKernel B S hS X Y)
    (definingIdealSheafIsoKernel_hom_comp_ι B S hS X Y)
    (structureModulePullbackMap B S hS (𝟙 X)) (structureModulePullbackMap_id B S hS X)
    (idealSheafMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY))
    (definingIdealSheaf B S hS X Z).ι
    (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Y (𝟙 X)
      (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY))
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y)).homEquiv _ _
      (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq))
    ((modulePushforward B S hS (subspaceInclusion B S hS X Y)).map
      (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W).ι)
    (mono_pushforward_ι B S hS Y W)
    (homEquiv_idealSheafMap_fac B S hS Y Z W p hsq)

/-- **The ideal-sheaf sequence of a chain of closed subspaces is exact in the middle.** -/
theorem exact_idealSheafShortComplex :
    (ShortComplex.mk
      (idealSheafMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
        (subspaceInclusion_homOfLe_square B S hS Y Z hZY))
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y)).homEquiv _ _
        (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq))
      (idealSheafMap_comp_homEquiv_idealSheafMap_eq_zero B S hS Y Z hZY W p hsq) :
    ShortComplex (Modules.{u, u} B S hS X.1 X.2)).Exact :=
  exact_of_isLimit_kernelFork B S hS _
    (isLimit_kernelFork_of_natIsoId (modulePullbackIdIso B S hS X)
    (definingIdealSheaf B S hS X Y).ι (structureProjection B S hS X Y)
    (kernel.ι (structureProjection B S hS X Y))
    (kernel.condition (structureProjection B S hS X Y))
    (kernelIsKernel (structureProjection B S hS X Y))
    (definingIdealSheafIsoKernel B S hS X Y)
    (definingIdealSheafIsoKernel_hom_comp_ι B S hS X Y)
    (structureModulePullbackMap B S hS (𝟙 X)) (structureModulePullbackMap_id B S hS X)
    (idealSheafMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY))
    (definingIdealSheaf B S hS X Z).ι (mono_definingIdealSheaf_ι B S hS X Z)
    (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Y (𝟙 X)
      (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY))
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y)).homEquiv _ _
      (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq))
    ((modulePushforward B S hS (subspaceInclusion B S hS X Y)).map
      (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W).ι)
    (mono_pushforward_ι B S hS Y W)
    (homEquiv_idealSheafMap_fac B S hS Y Z W p hsq)
    (idealSheafMap_comp_homEquiv_idealSheafMap_eq_zero B S hS Y Z hZY W p hsq))

/-- The transpose of the map `j^*𝓘_Z ⟶ 𝓘_W` of [Stacks Project, Tag 04CP] is an epimorphism as
soon as that map is: the unit of the adjunction of [Stacks Project, Tag 03D7] is an epimorphism
at every module by the essential-image clause of [Stacks Project, Tag 04CJ], part (3), and the
direct image along a closed immersion preserves epimorphisms. -/
theorem epi_homEquiv_idealSheafMap
    (hepi : Epi (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq)) :
    Epi ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y)).homEquiv _ _
      (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq)) :=
  epi_homEquiv_of_epi (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y))
    (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq)
    (epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS
      (subspaceInclusion B S hS X Y) Y.2.2
      (fun M hM ↦ essImage_modulePushforward_of_annihilatedByKerIdeal B S hS
        (subspaceInclusion B S hS X Y) Y.2.2 M hM)
      (definingIdealSheaf B S hS X Z).toSheafOfModules)
    (epi_modulePushforward_map B S hS (subspaceInclusion B S hS X Y) Y.2.2
      (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq) hepi)

/-- The left-hand square of comparison isomorphisms between the conormal sequence of the chain
and the inverse image of its sequence of defining ideal sheaves.  It is the naturality of
`AlgebraicGeometry.Space.conormalPullbackCompIso` at the map of defining ideal sheaves, read
through the defining equation of `AlgebraicGeometry.Space.conormalMap`. -/
theorem conormalSequence_comparison_square₁₂ :
    ((modulePullback B S hS p).map
          (conormalPullbackComparison B S hS Z Y (𝟙 X)
            (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
            (subspaceInclusion_homOfLe_square B S hS Y Z hZY)) ≫
        (conormalPullbackCompIso B S hS W Z (subspaceInclusion B S hS X Y) p hsq).hom.app
          ((modulePullback B S hS (𝟙 X)).obj
            (definingIdealSheaf B S hS X Y).toSheafOfModules)) ≫
      (modulePullback B S hS (subspaceInclusion B S hS
          (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W)).map
        ((modulePullback B S hS (subspaceInclusion B S hS X Y)).map
          (idealSheafMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
            (subspaceInclusion_homOfLe_square B S hS Y Z hZY))) =
    (modulePullback B S hS p).map
        (conormalMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
          (subspaceInclusion_homOfLe_square B S hS Y Z hZY)) ≫
      (conormalPullbackCompIso B S hS W Z (subspaceInclusion B S hS X Y) p hsq).hom.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  comp_natTrans_app_eq_of_fac
    (conormalPullbackCompIso B S hS W Z (subspaceInclusion B S hS X Y) p hsq).hom
    (idealSheafMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
      (subspaceInclusion_homOfLe_square B S hS Y Z hZY))
    ((modulePullback B S hS p).map
      (conormalPullbackComparison B S hS Z Y (𝟙 X)
        (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
        (subspaceInclusion_homOfLe_square B S hS Y Z hZY))) _
    ((congrArg (modulePullback B S hS p).map
        (conormalMap_eq B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
          (subspaceInclusion_homOfLe_square B S hS Y Z hZY))).trans
      ((modulePullback B S hS p).map_comp _ _))

/-- The right-hand square of comparison isomorphisms between the conormal sequence of the chain
and the inverse image of its sequence of defining ideal sheaves: the defining equation of
`AlgebraicGeometry.Space.conormalMap`. -/
theorem conormalSequence_comparison_square₂₃ :
    (conormalPullbackCompIso B S hS W Z (subspaceInclusion B S hS X Y) p hsq).hom.app
          (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
        (modulePullback B S hS (subspaceInclusion B S hS
            (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W)).map
          (idealSheafMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq) =
      conormalMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq ≫ 𝟙 _ :=
  (conormalMap_eq B S hS W Z (subspaceInclusion B S hS X Y) p hsq).symm.trans
    (Category.comp_id _).symm

/-- **The composite of the two arrows of the conormal sequence of a chain vanishes.**  This is
the vanishing of [Stacks Project, Tag 06BD] for an arbitrary upper subspace `W ⊆ Y` carried into
`Z` by a commutative square, of which
`AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero` — the clause of the tag — is the
instance at the inverse-image square.

The argument is the one of that instance, and uses nothing about the square beyond its
commutativity: by the composition law of part (3) of [Stacks Project, Tag 04G2],
`AlgebraicGeometry.Space.conormalMap_comp`, the composite is the map of [Stacks Project,
Tag 04CP] of the outer rectangle, read through an isomorphism; the lower edge of that rectangle
is `j ≫ 𝟙 X = j`, which factors through `Y` by the identity of `Y`, so that map vanishes by
`AlgebraicGeometry.Space.conormalMap_eq_zero_of_factorization`.

It is stated here, at the variable upper subspace, because the composite's first arrow is the
inverse image along `p`, and the inverse-image functor along the vertical morphism of the square
carries the source and target of `p` as implicit arguments: at the variable `p` they are the
projections of the subspaces, at `AlgebraicGeometry.Space.preimageProjection` they are the ones
its own type declares, and the elaborator does not cross between those two spellings inside
`CategoryTheory.Functor.map` within the heartbeat budget. -/
theorem conormalMap_comp_conormalMap_eq_zero_chain :
    (modulePullback B S hS p).map
        (conormalMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
          (subspaceInclusion_homOfLe_square B S hS Y Z hZY)) ≫
      conormalMap B S hS W Z (subspaceInclusion B S hS X Y) p hsq = 0 := by
  have houter : subspaceInclusion B S hS
          (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS) W ≫
        subspaceInclusion B S hS X Y ≫ 𝟙 X =
      (p ≫ (ObjectProperty.homMk (Subfunctor.homOfLe hZY) :
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))) ≫
        subspaceInclusion B S hS X Y := by
    rw [← Category.assoc, hsq, Category.assoc,
      subspaceInclusion_homOfLe_square B S hS Y Z hZY, Category.assoc]
  have hcomp := conormalMap_comp B S hS (subspaceInclusion B S hS X Y) (𝟙 X) W Z Y p
    (ObjectProperty.homMk (Subfunctor.homOfLe hZY)) hsq
    (subspaceInclusion_homOfLe_square B S hS Y Z hZY) houter
  have hvanish := conormalMap_eq_zero_of_factorization B S hS W Y
    (subspaceInclusion B S hS X Y ≫ 𝟙 X)
    (p ≫ ObjectProperty.homMk (Subfunctor.homOfLe hZY)) houter
    (𝟙 (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    (by rw [Category.id_comp, Category.comp_id])
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).mp (hcomp.symm.trans hvanish)

end Chain

/-! ### The sequence at the inverse-image square -/

section Preimage

variable {X : AlgebraicSpaces B S hS} (Y Z : ClosedSubspaces B S hS X.1) (hZY : Z.1 ≤ Y.1)

/-- **The sequence of defining ideal sheaves of the chain, pulled back to the inverse image, is
exact in the middle.**  The sequence `(𝟙 X)^*𝓘_Y ⟶ 𝓘_Z ⟶ j_*𝓘_W` of
`AlgebraicGeometry.Space.exact_idealSheafShortComplex` is exact in the middle and its second map
is an epimorphism; its inverse image along `j` has `𝓘_W` for last term, by the counit
isomorphism of [Stacks Project, Tag 04CJ], part (2), and inverse image preserves cokernels,
being a left adjoint, so exactness in the middle survives the two inverse images. -/
theorem exact_map_idealSheafSequence :
    (@ShortComplex.map _ _ _ _ _ _
      (ShortComplex.mk
        ((modulePullback B S hS (subspaceInclusion B S hS X Y)).map
          (idealSheafMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
            (subspaceInclusion_homOfLe_square B S hS Y Z hZY)))
        (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
          (subspaceInclusion B S hS X Y)
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))
        (comp_eq_zero_of_map_of_fac (modulePullback B S hS (subspaceInclusion B S hS X Y))
          (preservesZeroMorphisms_modulePullback B S hS (subspaceInclusion B S hS X Y)) _ _
          (idealSheafMap_comp_homEquiv_idealSheafMap_eq_zero B S hS Y Z hZY
            (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)
            (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
            (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)) _ _
          (map_homEquiv_comp_counit
            (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y))
            (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
              (subspaceInclusion B S hS X Y)
              (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
              (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)))))
      (modulePullback B S hS (subspaceInclusion B S hS
        (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
        (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)))
      (preservesZeroMorphisms_modulePullback B S hS (subspaceInclusion B S hS
        (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
        (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)))).Exact :=
  have hiso3 := isIso_modulePullbackAdjunction_counit B S hS
    (subspaceInclusion B S hS X Y) Y.2.2
    (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
      (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)).toSheafOfModules
  have _ := hiso3
  exact_map_modulePullback B S hS
    (subspaceInclusion B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
      (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)) _
    (exact_mk_of_exact_map B S hS (subspaceInclusion B S hS X Y) _
      (exact_idealSheafShortComplex B S hS Y Z hZY
        (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))
      (epi_homEquiv_idealSheafMap B S hS Y Z
        (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)
        (epi_idealSheafMap B S hS (subspaceInclusion B S hS X Y) Z))
      (asIso ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y)).counit.app
        (definingIdealSheaf B S hS (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
          (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)).toSheafOfModules)) _
      (map_homEquiv_comp_counit
        (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y))
        (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
          (subspaceInclusion B S hS X Y)
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))) _)
    (epi_idealSheafMap B S hS (subspaceInclusion B S hS X Y) Z)

/-- **The inverse image of the ideal-sheaf sequence, written out.**  This is
`AlgebraicGeometry.Space.exact_map_idealSheafSequence` with its short complex spelled by its two
morphisms rather than as the image of one under `CategoryTheory.ShortComplex.map`, so that the
transport of `CategoryTheory.Limits.exact_mk_of_squares` has no projection of a `ShortComplex`
to unfold. -/
theorem exact_mk_map_idealSheafSequence :
    (ShortComplex.mk
      ((modulePullback B S hS (subspaceInclusion B S hS
            (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
            (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z))).map
        ((modulePullback B S hS (subspaceInclusion B S hS X Y)).map
          (idealSheafMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
            (subspaceInclusion_homOfLe_square B S hS Y Z hZY))))
      ((modulePullback B S hS (subspaceInclusion B S hS
            (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
            (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z))).map
        (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
          (subspaceInclusion B S hS X Y)
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)))
      (map_comp_eq_zero
        (modulePullback B S hS (subspaceInclusion B S hS
          (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
          (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)))
        (preservesZeroMorphisms_modulePullback B S hS (subspaceInclusion B S hS
          (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS)
          (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z))) _ _
        (comp_eq_zero_of_map_of_fac (modulePullback B S hS (subspaceInclusion B S hS X Y))
          (preservesZeroMorphisms_modulePullback B S hS (subspaceInclusion B S hS X Y)) _ _
          (idealSheafMap_comp_homEquiv_idealSheafMap_eq_zero B S hS Y Z hZY
            (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)
            (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
            (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)) _ _
          (map_homEquiv_comp_counit
            (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Y))
            (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
              (subspaceInclusion B S hS X Y)
              (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
              (conormalEtaleRestrictionSquare B S hS
                (subspaceInclusion B S hS X Y) Z)))))).Exact :=
  exact_map_idealSheafSequence B S hS Y Z hZY

/-- **Exactness in the middle of [Stacks Project, Tag 06BD].**  Let `Y` and `Z` be closed
subspaces of an algebraic space `X` with `Z ⊆ Y`, let `j : Y ⟶ X` be the inclusion and let
`p : j⁻¹(Z) ⟶ Z` be the projection.  The conormal sequence of the pair,

`p^*(i^*𝒞_{Y/X}) ⟶ p^*𝒞_{Z/X} ⟶ 𝒞_{j⁻¹(Z)/Y}`,

is exact in the middle.

The sequence is the inverse image along `j`, and then along the inclusion of `j⁻¹(Z)`, of the
sequence of defining ideal sheaves `(𝟙 X)^*𝓘_Y ⟶ 𝓘_Z ⟶ j_*𝓘_{j⁻¹(Z)}`, which is exact in the
middle and whose second map is an epimorphism, so exactness in the middle survives both inverse
images (`AlgebraicGeometry.Space.exact_map_idealSheafSequence`, written out as
`AlgebraicGeometry.Space.exact_mk_map_idealSheafSequence`).  The identification of the two
sequences is the pair of squares
`AlgebraicGeometry.Space.conormalSequence_comparison_square₁₂` and
`AlgebraicGeometry.Space.conormalSequence_comparison_square₂₃`, whose vertical maps are
isomorphisms — the inverse image along `p` of
`AlgebraicGeometry.Space.conormalPullbackComparison` followed by a component of
`AlgebraicGeometry.Space.conormalPullbackCompIso`, that component at the defining ideal sheaf of
`Z`, and the identity — and the transport along them is
`CategoryTheory.Limits.exact_mk_of_squares`.

The companion clauses of the tag are
`AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero`, which says that the two arrows
compose to zero, and `AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces`, which says the
second is an epimorphism; with this clause the tag carries all three.

The source and target of the inverse-image functor along `p` are supplied explicitly, as the
projections of the two subspaces, and the vanishing is taken from
`AlgebraicGeometry.Space.conormalMap_comp_conormalMap_eq_zero_chain` rather than from the
clause-one instance; the implementation notes record why. -/
@[stacks 06BD "exactness at the middle term", sga "6 VIII 2.2" "partial"]
theorem exact_conormalShortComplex :
    (ShortComplex.mk
      ((@modulePullback B S hS
          (⟨(preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z).1.toFunctor,
              (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z).2.1⟩ :
            AlgebraicSpaces B S hS)
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).map
        (conormalMap B S hS Z Y (𝟙 X) (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
          (subspaceInclusion_homOfLe_square B S hS Y Z hZY)))
      (conormalMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
        (subspaceInclusion B S hS X Y)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))
      (conormalMap_comp_conormalMap_eq_zero_chain B S hS Y Z hZY
        (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))).Exact :=
  exact_mk_of_squares _ _ _
    (conormalSequence_comparison_square₁₂ B S hS Y Z hZY
      (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)
      (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
      (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))
    (conormalSequence_comparison_square₂₃ B S hS Y Z
      (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z)
      (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
      (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z))
    (isIso_comp_of _ _
      (isIso_map_of _ _
        (isIso_conormalPullbackComparison B S hS Z Y (𝟙 X)
          (ObjectProperty.homMk (Subfunctor.homOfLe hZY))
          (subspaceInclusion_homOfLe_square B S hS Y Z hZY)))
      (isIso_hom_app
        ((conormalPullbackCompIso B S hS
            (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
            (subspaceInclusion B S hS X Y)
            (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
            (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)).app
          ((modulePullback B S hS (𝟙 X)).obj
            (definingIdealSheaf B S hS X Y).toSheafOfModules))))
    (isIso_hom_app
      ((conormalPullbackCompIso B S hS
          (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
          (subspaceInclusion B S hS X Y)
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)).app
        (definingIdealSheaf B S hS X Z).toSheafOfModules))
    (isIso_hom_app (Iso.refl _))
    (exact_mk_map_idealSheafSequence B S hS Y Z hZY)

end Preimage

end AlgebraicGeometry.Space

end
