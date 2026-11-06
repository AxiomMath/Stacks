module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Presentation.Tautological
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RingPresheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherent presheaves of modules on a chaotic site

Let `C` be a category, viewed as a site with the chaotic (indiscrete) topology,
for which the coverings of an object `U` are exactly the families consisting of
isomorphisms. For this topology a sheaf is the same thing as a presheaf, so a
sheaf of rings (resp. of modules) is just a presheaf of rings (resp. of
modules). We therefore fix a presheaf of commutative rings
`O : Cᵒᵖ ⥤ CommRingCat` and a presheaf of modules `F` over it, and spell out
quasi-coherence of `F` directly in presheaf terms.

For a morphism `f : U ⟶ V` in `C` we write `O(f) : O(V) → O(U)` for the ring
restriction map, which makes `O(U)` an `O(V)`-algebra, and
`F(f) : F(V) → F(U)` for the module restriction map, which is semilinear over
`O(f)`, that is `F(f)(a • s) = O(f)(a) • F(f)(s)`.

## Main definitions

* `ChaoticQCoh.freeRank R I` is the free presheaf of `R`-modules `⊕_{i ∈ I} R`.
* `ChaoticQCoh.HasGlobalPresentation R G` says that the presheaf of `R`-modules
  `G` is the cokernel of a morphism between free presheaves of modules, i.e.
  that there is an exact sequence `⊕_J R ⟶ ⊕_I R ⟶ G ⟶ 0`.
* `ChaoticQCoh.canonicalMap O F f`, for `f : U ⟶ V`, is the canonical map
  `F(V) ⊗_{O(V)} O(U) ⟶ F(U)`, the unique `O(U)`-linear map sending `a ⊗ s` to
  `a • F(f)(s)`. It is the adjoint transpose of `F(f)` under the
  extension/restriction of scalars adjunction.
* `ChaoticQCoh.QuasiCoherent O F` says that for every object `U` of `C` the
  restriction `F|_{C/U}` to the slice category has a global presentation as a
  presheaf of `O|_{C/U}`-modules. This is the specialisation to the chaotic
  topology of the general notion of a quasi-coherent sheaf of modules, where the
  only coverings are families of isomorphisms, so that `{𝟙 U}` may be taken as
  the covering.

## Main results

* `ChaoticQCoh.quasiCoherent_iff_canonicalMap_isIso`: `F` is quasi-coherent if
  and only if the canonical map `F(V) ⊗_{O(V)} O(U) ⟶ F(U)` is an isomorphism
  for every morphism `f : U ⟶ V` of `C`.

## Implementation notes

The free presheaf of modules functor of Mathlib forces the universe of the
indexing types of a presentation, the universe of the values of the presheaf of
rings and the universe of the modules to agree; they are the single universe
`r` below. The universes of the objects and the morphisms of `C` are
independent of it.

## References

* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits TensorProduct

universe u v r

namespace ChaoticQCoh

variable {C : Type u} [Category.{v} C]

/-! ## Free presheaves of modules and global presentations

These are stated for an arbitrary presheaf of rings `R : Cᵒᵖ ⥤ RingCat`; the
ringed-site instance specialises `R` to the underlying presheaf of rings of `O`.
-/

/-- The free presheaf of modules `⊕_{i ∈ I} R` of rank indexed by a set `I`,
obtained as the free presheaf of modules on the constant presheaf of sets with
value `I`. -/
noncomputable def freeRank (R : Cᵒᵖ ⥤ RingCat.{r}) (I : Type r) : PresheafOfModules.{r} R :=
  (PresheafOfModules.free R).obj ((Functor.const Cᵒᵖ).obj I)

/-- A presheaf of `R`-modules `G` **has a global presentation** if there exist
index sets `I, J` and a presentation
  `⊕_J R ⟶ ⊕_I R ⟶ G ⟶ 0`
that is exact (the two-term complex is exact at `⊕_I R`, and the map to `G` is an
epimorphism, encoding exactness at `G` together with surjectivity). This is the
statement that `G` is the cokernel of a homomorphism between free modules. -/
def HasGlobalPresentation (R : Cᵒᵖ ⥤ RingCat.{r}) (G : PresheafOfModules.{r} R) : Prop :=
  ∃ (I J : Type r) (a : freeRank R J ⟶ freeRank R I) (b : freeRank R I ⟶ G)
    (w : a ≫ b = 0), (ShortComplex.mk a b w).Exact ∧ Epi b

/-! ## The ringed site `(C, O)` -/

-- A sheaf of commutative rings on the chaotic site `C`.
variable (O : Cᵒᵖ ⥤ CommRingCat.{r})

/-! The underlying presheaf of (not-necessarily-commutative) rings `O ⋙ forget₂ CommRingCat
RingCat` of `O` is defined once, as `Stacks.PresheafOfRings.ringPresheaf`; it
is made available here under the name `ChaoticQCoh.ringPresheaf` that this file and its
descendants use. -/

export Stacks.PresheafOfRings (ringPresheaf)

-- A sheaf of `O`-modules on the chaotic site `C`.
variable (F : PresheafOfModules.{r} (ringPresheaf O))

/-- For a morphism `f : U ⟶ V` of `C`, the ring restriction map
`O(f) : O(V) → O(U)`, regarded as a `RingHom`. This makes `O(U)` an
`O(V)`-algebra. -/
noncomputable abbrev ringRestriction {U V : C} (f : U ⟶ V) :
    O.obj (Opposite.op V) →+* O.obj (Opposite.op U) :=
  (O.map f.op).hom

/-! ## Definition 1: the canonical map -/

/-- The canonical map
  `c_f : F(V) ⊗_{O(V)} O(U) ⟶ F(U)`,
defined as the adjoint transpose of the restriction map `F(f) : F(V) ⟶
restrictScalars(O(f)) F(U)` under the extension/restriction of scalars
adjunction `(- ⊗_{O(V)} O(U)) ⊣ restrictScalars(O(f))`. -/
noncomputable def canonicalMap {U V : C} (f : U ⟶ V) :
    (ModuleCat.extendScalars (ringRestriction O f)).obj (F.obj (Opposite.op V)) ⟶
      F.obj (Opposite.op U) :=
  ((ModuleCat.extendRestrictScalarsAdj (ringRestriction O f)).homEquiv _ _).symm (F.map f.op)

/-- Correctness of `canonicalMap`: it is determined on simple tensors by
`c_f (s ⊗ a) = a • F(f)(s)`, where the right-hand side uses the `O(U)`-module
structure of `F(U)`. -/
theorem canonicalMap_tmul {U V : C} (f : U ⟶ V)
    (s : F.obj (Opposite.op V)) (a : O.obj (Opposite.op U)) :
    (canonicalMap O F f).hom (a ⊗ₜ s)
      = a • (show (F.obj (Opposite.op U) : Type r) from F.map f.op s) := by
  -- Unfold the adjoint transpose via the counit: `(adj.homEquiv _ _).symm g = F.map g ≫ counit`.
  -- On `a ⊗ₜ s` the extendScalars functor sends it to `a ⊗ₜ (F.map f.op s)` and the counit of the
  -- extend/restrict adjunction sends `a ⊗ₜ y ↦ a • y`; the last step is `rfl` since the counit is
  -- literally `TensorProduct.lift (fun a => fun y => a • y)`.
  rw [canonicalMap, Adjunction.homEquiv_counit]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.ExtendScalars.map_tmul]
  rfl

/-! ## Definition 3: quasi-coherence in the chaotic topology -/

/-- The restriction `F|_{C/U}` of `F` to the slice category `C/U`, a presheaf of
modules over the restricted presheaf of rings `O|_{C/U} = (Over.forget U).op ⋙ O`.
-/
@[sga "3 I 3.1.4"]
noncomputable def restrictToSlice (U : C) :
    PresheafOfModules.{r} ((Over.forget U).op ⋙ ringPresheaf O) :=
  (PresheafOfModules.pushforward₀ (Over.forget U) (ringPresheaf O)).obj F

/-- `F` is **quasi-coherent** (in the chaotic topology) if for every object `U`
of `C`, the restriction `F|_{C/U}` to the slice category has a global
presentation as a sheaf of `O|_{C/U}`-modules. -/
def QuasiCoherent : Prop :=
  ∀ U : C, HasGlobalPresentation ((Over.forget U).op ⋙ ringPresheaf O) (restrictToSlice O F U)

/-! ## Main Statement (Stacks Tag `0GZN`, Lemma 18.24.3)

The proof splits into the two implications, each isolated as a named sub-lemma
below.  Both directions rest on the same chaotic-topology computational core:

* **Objectwise (co)limits / exactness.**  On the chaotic site, a (co)limit of
  presheaves of modules is computed objectwise, and a sequence of presheaves is
  exact iff it is exact after evaluating at every object `W`.  In particular the
  "evaluate at `W`" functor `G ↦ G(W)` is exact and commutes with the free
  construction: `(freeRank R I)(W) = ⊕_{i ∈ I} R(W)` as `R(W)`-modules.

* **Slice sections.**  For `U : C`, an object `(x : X ⟶ U)` of the slice `C/U`,
  one has `(restrictToSlice O F U)(op (Over.mk x)) = F(X)` and
  `((Over.forget U).op ⋙ ringPresheaf O)(op (Over.mk x)) = O(X)`, compatibly with
  the canonical maps: the structure map of `restrictToSlice` along a slice
  morphism induced by `g : X ⟶ Y` over `U` is just `F.map g.op`.

* **Base change is right exact.**  `- ⊗_{O(V)} O(U)` is right exact, so it
  carries a presentation `⊕_J O(V) → ⊕_I O(V) → F(V) → 0` to an exact sequence
  `⊕_J O(U) → ⊕_I O(U) → F(V) ⊗_{O(V)} O(U) → 0`; comparing its cokernel with the
  presentation of `F(U)` is exactly the assertion that `c_f` is an isomorphism.
-/

/-- **Reflection of exactness (chaotic site).**  A short complex of presheaves of
modules is exact as soon as it is exact after evaluation at every object `X`
(exactness of presheaves of modules is objectwise).  Proof outline:
`ShortComplex.exact_iff_isZero_homology`; evaluation preserves homology
(`ShortComplex.mapHomologyIso`, since `(evaluation R X).PreservesLeftHomologyOf`
is an instance); a presheaf of modules is zero iff zero at every object
(`PresheafOfModules.hom_ext` / `IsZero.iff_id_eq_zero`, using `evaluation_obj`). -/
@[sga "3 I 5.2" "partial"]
theorem exact_of_evaluation (R : Cᵒᵖ ⥤ RingCat.{r})
    (S : ShortComplex (PresheafOfModules.{r} R))
    (he : ∀ X : Cᵒᵖ, (S.map (PresheafOfModules.evaluation R X)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  rw [IsZero.iff_id_eq_zero]
  apply PresheafOfModules.hom_ext
  intro X
  have hex := he X
  rw [ShortComplex.exact_iff_isZero_homology] at hex
  have hiso := S.mapHomologyIso (PresheafOfModules.evaluation R X)
  have hz : IsZero ((PresheafOfModules.evaluation R X).obj S.homology) :=
    IsZero.of_iso hex hiso.symm
  rw [IsZero.iff_id_eq_zero] at hz
  exact hz

/-- **Reflection of epi (chaotic site).**  A morphism of presheaves of modules is
an epimorphism as soon as it is epi after evaluation at every object `X`
(objectwise (co)kernels / cokernel-is-zero on the chaotic site).  Same objectwise
strategy as `exact_of_evaluation` (epi ⇔ cokernel is zero, computed objectwise). -/
theorem epi_of_evaluation {R : Cᵒᵖ ⥤ RingCat.{r}} {G H : PresheafOfModules.{r} R}
    (φ : G ⟶ H) (he : ∀ X : Cᵒᵖ, Epi ((PresheafOfModules.evaluation R X).map φ)) : Epi φ := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro Z g hg
  apply PresheafOfModules.hom_ext
  intro X
  have h2 := he X
  have key : (PresheafOfModules.evaluation R X).map g = 0 := by
    rw [← cancel_epi ((PresheafOfModules.evaluation R X).map φ)]
    rw [← Functor.map_comp, hg, Functor.map_zero, comp_zero]
  simpa using key

/-! ### Decomposition of the core construction `slicePresentation_data_of_isIso`

The construction is broken into a pure-algebra leaf plus the presheaf-level
construction:

* `baseChange_presentation_exact` — **pure-algebra leaf**: right-exactness of
  base change of a free presentation.  For a
  ring hom `φ : R →+* S` and an exact presentation `(J →₀ R) → (I →₀ R) → M → 0`,
  the base-changed sequence `(J →₀ S) → (I →₀ S) → M ⊗[R] S → 0` (via
  `finsuppScalarLeft`) is exact.  Provable in isolation from `rTensor` exactness +
  `LinearMap.rTensor_surjective` + `finsuppScalarLeft`.  Reusable in the `⇒`
  direction too.

* `slicePresentation_data_of_isIso` — **the presheaf-level construction**: pick
  the tautological `O(V)`-presentation of `F(V)`; promote `a₀, b₀` to slice
  presheaf maps via `PresheafOfModules.freeObjDesc` applied to the natural
  transformation of global sections `(g : Y ⟶ V) ↦ (i ↦ F(g)(eᵢ))` resp.
  `(g) ↦ (j ↦ base-change of ρ(δⱼ))`.  Objectwise: evaluation at `X = (g : Y ⟶ V)`
  gives the base change of the chosen presentation, exact by
  `baseChange_presentation_exact`; the iso `c_g` (`canonicalMap_tmul`) identifies
  the cokernel with `F(Y)`, giving objectwise exactness and objectwise epi of `b`.
-/

/-- **Pure-algebra leaf.**  Base change `- ⊗[R] S` of a free
presentation is right exact, after the canonical `finsuppScalarLeft`
identification of the free terms.  Given a ring hom `φ : R →+* S`, an `R`-module
`M`, and an exact presentation `(J →₀ R) →(ρ) (I →₀ R) →(π) M → 0` (i.e.
`Function.Exact ρ π` with `π` surjective), the base-changed maps fit into an
exact sequence `(J →₀ S) → (I →₀ S) → M ⊗[R] S → 0`.

Here the base-changed maps are `Finsupp.mapRange.linearMap`-style coordinatewise
applications of `φ`; concretely they are `ρ` resp. `π` tensored with `S` and
transported across `finsuppScalarLeft R S _ : (K →₀ R) ⊗[R] S ≃ₗ[S] (K →₀ S)`.
The statement is phrased via `LinearMap.rTensor`/`lTensor` so it can be applied to
the slice-object evaluation in `slicePresentation_data_of_isIso`. -/
theorem baseChange_presentation_exact
    {R : Type r} [CommRing R] {S : Type r} [CommRing S] (φ : R →+* S)
    {M : Type r} [AddCommGroup M] [Module R M]
    {I J : Type r} (ρ : (J →₀ R) →ₗ[R] (I →₀ R)) (π : (I →₀ R) →ₗ[R] M)
    (hexact : Function.Exact ρ π) (hsurj : Function.Surjective π) :
    letI := φ.toAlgebra
    Function.Exact
        (LinearMap.rTensor S ρ : ((J →₀ R) ⊗[R] S) →ₗ[R] ((I →₀ R) ⊗[R] S))
        (LinearMap.rTensor S π : ((I →₀ R) ⊗[R] S) →ₗ[R] (M ⊗[R] S)) ∧
      Function.Surjective (LinearMap.rTensor S π) := by
  let := φ.toAlgebra
  exact ⟨rTensor_exact S hexact hsurj, LinearMap.rTensor_surjective S hsurj⟩

/-- **Natural transformation underlying `b`.**  For
the chosen generators `e : I → F(V)`, this is the family of global sections
`X = (g : Y ⟶ V) ↦ (i ↦ F(g)(eᵢ))` of the slice-restricted module
`restrictToSlice O F V`, packaged as a morphism into its underlying presheaf of
abelian groups.  Naturality is functoriality of `F` together with the slice
identity `φ.left ≫ W.hom = W'.hom` (`Over.w`). -/
noncomputable def bNat (V : C) (I : Type r) (e : I → F.obj (Opposite.op V)) :
    (Functor.const (Over V)ᵒᵖ).obj I ⟶ (restrictToSlice O F V).presheaf ⋙ forget Ab where
  app W := TypeCat.ofHom (fun (i : I) =>
      (show (F.obj (Opposite.op W.unop.left) : Type r) from F.map (W.unop.hom).op (e i)))
  naturality := by
    intro W W' φ
    ext i
    simp only [Functor.const_obj_map, Functor.comp_map]
    change F.map (W'.unop.hom).op (e i)
      = (forget Ab).map ((restrictToSlice O F V).presheaf.map φ) (F.map (W.unop.hom).op (e i))
    have hr : (forget Ab).map ((restrictToSlice O F V).presheaf.map φ) (F.map (W.unop.hom).op (e i))
        = F.map ((Over.forget V).op.map φ) (F.map (W.unop.hom).op (e i)) := rfl
    have hmor : W.unop.hom.op ≫ (Over.forget V).op.map φ = W'.unop.hom.op := by
      apply Quiver.Hom.unop_inj
      rw [unop_comp]
      change (Over.forget V).map φ.unop ≫ W.unop.hom = W'.unop.hom
      exact Over.w φ.unop
    rw [hr]
    have hcomp : F.map ((Over.forget V).op.map φ) (F.map (W.unop.hom).op (e i))
        = F.map (W.unop.hom.op ≫ (Over.forget V).op.map φ) (e i) := by
      rw [F.map_comp]
      rfl
    rw [hcomp, hmor]
    rfl

/-- **Natural transformation underlying `a`.**  For
the chosen relations `ρv : J → (I →₀ O(V))`, this assigns to each slice object
`W` the restriction of the global section `ρv j ∈ (freeRank _ I)(𝟙 V)` along the
unique slice morphism `W → 𝟙 V` (the terminal object `Over.mk (𝟙 V)`).
Naturality is automatic: it is functoriality of the free presheaf together with
uniqueness of morphisms into the terminal object. -/
noncomputable def aNat (V : C) (I J : Type r)
    (ρv : J → (I →₀ (O.obj (Opposite.op V) : Type r))) :
    (Functor.const (Over V)ᵒᵖ).obj J ⟶
      (freeRank ((Over.forget V).op ⋙ ringPresheaf O) I).presheaf ⋙ forget Ab where
  app W := TypeCat.ofHom (fun (j : J) =>
    (forget Ab).map ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) I).presheaf.map
        ((Over.homMk W.unop.hom (by simp) : W.unop ⟶ Over.mk (𝟙 V)).op))
      (show ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) I).presheaf ⋙ forget Ab).obj
          (Opposite.op (Over.mk (𝟙 V))) from ρv j))
  naturality := by
    intro W W' φ
    ext j
    simp only [Functor.const_obj_map, Functor.comp_map]
    have hmor : (Over.homMk W'.unop.hom (by simp) : W'.unop ⟶ Over.mk (𝟙 V)).op
        = (Over.homMk W.unop.hom (by simp) : W.unop ⟶ Over.mk (𝟙 V)).op ≫ φ := by
      apply Quiver.Hom.unop_inj
      rw [unop_comp]
      ext
      change W'.unop.hom = φ.unop.left ≫ W.unop.hom
      rw [Over.w φ.unop]
    rw [hmor, Functor.map_comp]
    rfl

/-- The chosen tautological `O(V)`-presentation of the `O(V)`-module `F(V)`.
Generators `slicePres_P.G = F(V)` (all elements), relations `slicePres_P.R`.  This
is the single presentation that is base-changed coherently across the slice. -/
noncomputable def slicePres_P (V : C) :
    Module.Presentation (O.obj (Opposite.op V) : Type r) (F.obj (Opposite.op V) : Type r) :=
  Module.Presentation.tautological (O.obj (Opposite.op V)) (F.obj (Opposite.op V))

/-- The presheaf-of-modules map `b : freeRank _ I ⟶ restrictToSlice O F V` of the
slice presentation, built via `freeObjDesc` from `bNat` (the family
`X=(g:Y→V) ↦ (i ↦ F(g)(eᵢ))`). -/
noncomputable def slicePres_b (V : C) :
    freeRank ((Over.forget V).op ⋙ ringPresheaf O) (slicePres_P O F V).G ⟶
      restrictToSlice O F V :=
  PresheafOfModules.freeObjDesc (bNat O F V (slicePres_P O F V).G (slicePres_P O F V).var)

/-- The presheaf-of-modules map `a : freeRank _ J ⟶ freeRank _ I` of the slice
presentation, built via `freeObjDesc` from `aNat` (the relation family
`X=(g:Y→V) ↦ (j ↦ Σᵢ O(g)(ρᵢⱼ)δᵢ)`, i.e. base change of `ρ(δⱼ)`). -/
noncomputable def slicePres_a (V : C) :
    freeRank ((Over.forget V).op ⋙ ringPresheaf O) (slicePres_P O F V).R ⟶
      freeRank ((Over.forget V).op ⋙ ringPresheaf O) (slicePres_P O F V).G :=
  PresheafOfModules.freeObjDesc
    (aNat O V (slicePres_P O F V).G (slicePres_P O F V).R
      (fun j => (slicePres_P O F V).map (Finsupp.single j 1)))

/-- In a free module, `single k r` is `r` times the basis vector `freeMk k`. -/
private theorem single_eq_smul_freeMk {R : Type r} [Ring R] {K : Type r} (k : K) (r : R) :
    (Finsupp.single k r : (ModuleCat.free R).obj K) = r • ModuleCat.freeMk k :=
  (Finsupp.smul_single_one k r).symm

/-- The composite `slicePres_a O F V ≫ slicePres_b O F V` of the two maps of the slice
presentation is zero. -/
theorem slicePres_comp_zero (V : C) :
    slicePres_a O F V ≫ slicePres_b O F V = 0 := by
  apply PresheafOfModules.hom_ext
  intro X
  rw [PresheafOfModules.comp_app]
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro j r
  rw [single_eq_smul_freeMk, map_smul, map_smul]
  congr 1
  rw [PresheafOfModules.zero_app]
  show (slicePres_b O F V).app X ((slicePres_a O F V).app X (ModuleCat.freeMk j)) = 0
  -- Let `W₀` be the terminal slice object `Over.mk (𝟙 V)`, and `φ₀ : W₀ ⟶ X` the
  -- canonical slice morphism induced by `X.unop.hom`.
  set W₀ : (Over V)ᵒᵖ := Opposite.op (Over.mk (𝟙 V)) with hW₀
  set φ₀ : W₀ ⟶ X := (Over.homMk X.unop.hom (by simp) : X.unop ⟶ Over.mk (𝟙 V)).op with hφ₀
  -- The relation `ρ j = relation j`, an element of `(freeRank _ G)(W₀)`.
  set ρj : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) (slicePres_P O F V).G).obj W₀ : Type r)
      := (slicePres_P O F V).map (Finsupp.single j 1) with hρj
  -- `a.app X (freeMk j)` is the restriction of `ρ j` (which lives at `W₀`) along `φ₀`.
  have haval : (slicePres_a O F V).app X (ModuleCat.freeMk j)
      = ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) (slicePres_P O F V).G).map φ₀).hom ρj := by
    rw [slicePres_a, PresheafOfModules.freeObjDesc_app]
    erw [ModuleCat.freeDesc_apply]
    rfl
  rw [haval]
  -- By naturality of `b`, this equals the restriction along `φ₀` of `b.app W₀ (ρ j)`.
  rw [PresheafOfModules.naturality_apply]
  -- It remains to show `b.app W₀ (ρ j) = 0`, then `map φ₀ 0 = 0`.
  have hbW₀ : (slicePres_b O F V).app W₀ ρj = 0 := by
    rw [slicePres_b, PresheafOfModules.freeObjDesc_app, hρj, Module.Relations.map_single]
    -- `freeDesc (bNat.app W₀)` agrees with the tautological solution's `π` on generators,
    -- because `bNat.app W₀ g = F.map (𝟙 V).op (var g) = var g`.
    have hπ : (ModuleCat.freeDesc
        ((bNat O F V (slicePres_P O F V).G (slicePres_P O F V).var).app W₀)).hom
        = (slicePres_P O F V).toSolution.π := by
      apply Finsupp.lhom_ext
      intro g s
      rw [single_eq_smul_freeMk, map_smul, map_smul]
      congr 1
      erw [ModuleCat.freeDesc_apply]
      show F.map ((Over.mk (𝟙 V)).hom).op ((slicePres_P O F V).var g)
        = (slicePres_P O F V).toSolution.π (Finsupp.single g 1)
      rw [Module.Relations.Solution.π_single]
      show F.map ((Over.mk (𝟙 V)).hom).op ((slicePres_P O F V).var g)
        = (slicePres_P O F V).var g
      have hid : ((Over.mk (𝟙 V)).hom).op = 𝟙 (Opposite.op (Over.mk (𝟙 V)).left) := rfl
      rw [hid]
      erw [F.map_id]
      rfl
    have hfin : (ModuleCat.freeDesc
        ((bNat O F V (slicePres_P O F V).G (slicePres_P O F V).var).app W₀)).hom
          ((slicePres_P O F V).relation j) = 0 := by
      rw [hπ]
      exact Module.Relations.Solution.π_relation _ _
    exact hfin
  rw [hbW₀, map_zero]

/-- Objectwise formula for `b` on a generator `freeMk i`: it is `F(g)(i)` where
`g = X.unop.hom`. -/
theorem slicePres_b_app_freeMk (V : C) (X : (Over V)ᵒᵖ) (i : (slicePres_P O F V).G) :
    (slicePres_b O F V).app X (ModuleCat.freeMk i)
      = (show (F.obj (Opposite.op X.unop.left) : Type r) from
          F.map (X.unop.hom).op ((slicePres_P O F V).var i)) := by
  rw [slicePres_b, PresheafOfModules.freeObjDesc_app]
  erw [ModuleCat.freeDesc_apply]
  rfl

/-- Objectwise formula for `a` on a generator `freeMk j`: it is the restriction
along the canonical slice morphism `φ₀ : Over.mk (𝟙 V) ⟶ X` of the relation
`ρ j = slicePres_P.map (single j 1)`. -/
theorem slicePres_a_app_freeMk (V : C) (X : (Over V)ᵒᵖ) (j : (slicePres_P O F V).R) :
    (slicePres_a O F V).app X (ModuleCat.freeMk j)
      = ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) (slicePres_P O F V).G).map
          ((Over.homMk X.unop.hom (by simp) : X.unop ⟶ Over.mk (𝟙 V)).op)).hom
          ((slicePres_P O F V).map (Finsupp.single j 1)) := by
  rw [slicePres_a, PresheafOfModules.freeObjDesc_app]
  erw [ModuleCat.freeDesc_apply]
  rfl

/-- Coordinatewise formula for the structure map of a free presheaf of modules on
a generator `freeMk k`: it is preserved. -/
theorem freeRank_map_freeMk (R : Cᵒᵖ ⥤ RingCat.{r}) (K : Type r) {X Y : Cᵒᵖ} (φ : X ⟶ Y) (k : K) :
    ((freeRank R K).map φ).hom (ModuleCat.freeMk k) = ModuleCat.freeMk k := by
  unfold freeRank
  simp only [Functor.const_obj_obj]
  erw [ModuleCat.freeDesc_apply]
  rfl

/-- Coordinatewise formula for the structure map of a free presheaf of modules on
`single k r`: apply the ring map in the coordinate. -/
theorem freeRank_map_single (R : Cᵒᵖ ⥤ RingCat.{r}) (K : Type r) {X Y : Cᵒᵖ} (φ : X ⟶ Y) (k : K)
    (r : (R.obj X : Type r)) :
    ((freeRank R K).map φ).hom (Finsupp.single k r) = Finsupp.single k ((R.map φ).hom r) := by
  rw [single_eq_smul_freeMk, PresheafOfModules.map_smul, freeRank_map_freeMk,
    ← Finsupp.smul_single_one]
  rfl

/-- Transport of `Function.Exact` across bijections intertwining the maps. -/
theorem exact_transport {M N P M' N' P' : Type r} (f : M → N) (g : N → P)
    (f' : M' → N') (g' : N' → P') [Zero P] [Zero P']
    (eM : M ≃ M') (eN : N ≃ N') (eP : P ≃ P')
    (hf : ∀ m, eN (f m) = f' (eM m)) (hg : ∀ n, eP (g n) = g' (eN n))
    (h0 : ∀ p, eP p = 0 ↔ p = 0)
    (H : Function.Exact f' g') : Function.Exact f g := by
  intro n
  constructor
  · intro hn
    have hz : g' (eN n) = 0 := by rw [← hg, hn, (h0 _).mpr rfl]
    obtain ⟨m', hm'⟩ := (H (eN n)).mp hz
    refine ⟨eM.symm m', ?_⟩
    apply eN.injective
    rw [hf, Equiv.apply_symm_apply, hm']
  · rintro ⟨m, rfl⟩
    have hz : g' (f' (eM m)) = 0 := (H (f' (eM m))).mpr ⟨eM m, rfl⟩
    rw [← hf, ← hg] at hz
    exact (h0 _).mp hz

/-- `finsuppScalarLeft` on a simple tensor `single k c ⊗ₜ s` is `single k (c • s)`. -/
theorem finsuppScalarLeft_single_tmul (R : Type r) [CommRing R] (S : Type r) [CommRing S]
    [Algebra R S] (ι : Type r) [DecidableEq ι] (k : ι) (c : R) (s : S) :
    finsuppScalarLeft R S ι (Finsupp.single k c ⊗ₜ[R] s) = Finsupp.single k (c • s) := by
  rw [finsuppScalarLeft_apply_tmul, Finsupp.sum_single_index]
  simp

/-- The sections of `(Over.forget V).op ⋙ ringPresheaf O` over `X` act through `O(X.left)`
(instance search no longer unfolds `⋙` here). -/
private noncomputable instance moduleRestrictScalarsSliceObj {V : C} (X : (Over V)ᵒᵖ)
    {R : Type r} [Ring R] (f : R →+* (((Over.forget V).op ⋙ ringPresheaf O).obj X : Type r))
    (M : ModuleCat.{r} (((Over.forget V).op ⋙ ringPresheaf O).obj X)) :
    Module (O.obj (Opposite.op X.unop.left) : Type r) ((ModuleCat.restrictScalars f).obj M) :=
  inferInstanceAs (Module (((Over.forget V).op ⋙ ringPresheaf O).obj X)
    ((ModuleCat.restrictScalars f).obj M))

/-- Restricting a coordinate vector along the canonical slice morphism `𝟙 V ⟶ X` and scaling by
`c` is `finsuppScalarLeft` of the base change of the vector along `O(g)`, `g = X.unop.hom`. -/
private theorem smul_freeRank_map_eq_finsuppScalarLeft_tmul {V : C} (X : (Over V)ᵒᵖ)
    (K : Type r) [DecidableEq K] (c : (O.obj (Opposite.op X.unop.left) : Type r))
    (v : K →₀ (O.obj (Opposite.op V) : Type r)) :
    letI := (ringRestriction O X.unop.hom).toAlgebra
    c • (((freeRank ((Over.forget V).op ⋙ ringPresheaf O) K).map
        (Over.homMk X.unop.hom (by simp) : X.unop ⟶ Over.mk (𝟙 V)).op).hom v)
      = finsuppScalarLeft (O.obj (Opposite.op V) : Type r)
          (O.obj (Opposite.op X.unop.left) : Type r) K
          (v ⊗ₜ[(O.obj (Opposite.op V) : Type r)] c) := by
  let := (ringRestriction O X.unop.hom).toAlgebra
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero, smul_zero, TensorProduct.zero_tmul, LinearEquiv.map_zero]
  | add p q hp hq =>
      rw [map_add, smul_add, hp, hq, TensorProduct.add_tmul, LinearEquiv.map_add]
  | single k d =>
      rw [freeRank_map_single]
      change c • Finsupp.single k
        (algebraMap (O.obj (Opposite.op V) : Type r) (O.obj (Opposite.op X.unop.left) : Type r) d)
          = _
      rw [Finsupp.smul_single, smul_eq_mul, finsuppScalarLeft_single_tmul, Algebra.smul_def,
        mul_comm]

/-- For every slice object `X = (g : Y ⟶ V)`, the evaluated complex
`⊕_J O(Y) → ⊕_I O(Y) → F(Y)` of the slice presentation is exact and its last map is epi.
Identify it (via `finsuppScalarLeft`) with the base change of the chosen
presentation along `O(g)`, exact by `baseChange_presentation_exact`; transport the
cokernel across the iso `c_g` (`canonicalMap_tmul`, iso by `h`). -/
private theorem slicePres_objectwise_exact_and_epi
    (h : ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso (canonicalMap O F f)) (V : C)
    (X : (Over V)ᵒᵖ) :
    ((ShortComplex.mk (slicePres_a O F V) (slicePres_b O F V) (slicePres_comp_zero O F V)).map
      (PresheafOfModules.evaluation ((Over.forget V).op ⋙ ringPresheaf O) X)).Exact ∧
    Epi ((PresheafOfModules.evaluation ((Over.forget V).op ⋙ ringPresheaf O) X).map
      (slicePres_b O F V)) := by
  classical
  set Y : C := X.unop.left with hY
  set g₀ : Y ⟶ V := X.unop.hom with hg₀
  let : Algebra (O.obj (Opposite.op V) : Type r) (O.obj (Opposite.op Y) : Type r) :=
    (ringRestriction O g₀).toAlgebra
  set P := slicePres_P O F V with hP
  -- the base-change exactness of the chosen tautological presentation along O(g₀)
  have hbc := baseChange_presentation_exact (R := (O.obj (Opposite.op V) : Type r))
    (S := (O.obj (Opposite.op Y) : Type r)) (ringRestriction O g₀)
    (M := (F.obj (Opposite.op V) : Type r)) P.map P.toSolution.π
    P.toIsPresentation.exact P.toIsPresentation.surjective_π
  -- The three transport equivalences between the evaluated complex and the
  -- base-changed complex.
  set eR : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) P.R).obj X : Type r) ≃
      ((P.R →₀ (O.obj (Opposite.op V) : Type r)) ⊗[(O.obj (Opposite.op V) : Type r)]
        (O.obj (Opposite.op Y) : Type r)) :=
    (finsuppScalarLeft (O.obj (Opposite.op V) : Type r) (O.obj (Opposite.op Y) : Type r)
      P.R).symm.toEquiv with heR
  set eG : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) P.G).obj X : Type r) ≃
      ((P.G →₀ (O.obj (Opposite.op V) : Type r)) ⊗[(O.obj (Opposite.op V) : Type r)]
        (O.obj (Opposite.op Y) : Type r)) :=
    (finsuppScalarLeft (O.obj (Opposite.op V) : Type r) (O.obj (Opposite.op Y) : Type r)
      P.G).symm.toEquiv with heG
  set eP : ((restrictToSlice O F V).obj X : Type r) ≃
      ((F.obj (Opposite.op V) : Type r) ⊗[(O.obj (Opposite.op V) : Type r)]
        (O.obj (Opposite.op Y) : Type r)) :=
    ((asIso (canonicalMap O F g₀)).toLinearEquiv.symm.toEquiv).trans
      (TensorProduct.comm (O.obj (Opposite.op V) : Type r) (O.obj (Opposite.op Y) : Type r)
        (F.obj (Opposite.op V) : Type r)).toEquiv with heP
  -- **Identity A** (commuting square for `a`): the evaluated map `aₓ` intertwines
  -- with `rTensor P.map` across `eR, eG`.  Plan: reduce to generators `z = single j s`
  -- (`Finsupp`/`TensorProduct` additive ext); LHS via `slicePres_a_app_freeMk` +
  -- `freeRank_map_single` (coordinatewise `O(g₀)`); RHS via `finsuppScalarLeft.symm`
  -- (`finsuppScalarLeft_symm_apply_single` / `_symm_single`) + `LinearMap.rTensor_tmul`;
  -- both reduce to coordinatewise commutativity `φ(r)·s·φ((ρⱼ)ᵢ) = φ(r·(ρⱼ)ᵢ)·s` in `O(Y)`.
  have hIdA : ∀ z, eG ((slicePres_a O F V).app X z)
      = (LinearMap.rTensor (O.obj (Opposite.op Y) : Type r) P.map) (eR z) := by
    intro z
    rw [heG, heR]
    simp only [LinearEquiv.coe_toEquiv]
    induction z using Finsupp.induction_linear with
    | zero =>
        repeat (first | erw [LinearEquiv.map_zero] | erw [map_zero])
    | add p q hp hq =>
        simp only [map_add]
        rw [hp, hq]
    | single j r =>
        -- Notation: φ₀ the canonical slice morphism, v the relation P.map (single j 1).
        set φ₀ : (Opposite.op (Over.mk (𝟙 V))) ⟶ X :=
          (Over.homMk X.unop.hom (by simp) : X.unop ⟶ Over.mk (𝟙 V)).op with hφ₀
        set v : (P.G →₀ (O.obj (Opposite.op V) : Type r)) := P.map (Finsupp.single j 1) with hv
        -- Rewrite the RHS to the simple tensor `v ⊗ₜ r`.
        conv_rhs => erw [finsuppScalarLeft_symm_apply_single]
        rw [LinearMap.rTensor_tmul]
        -- Cancel `L_G.symm` on the LHS: reduce to `aₓ (single j r) = L_G (v ⊗ₜ r)`.
        rw [LinearEquiv.symm_apply_eq]
        -- LHS: `single j r = r • freeMk j`, pull `r` out, apply `slicePres_a_app_freeMk`.
        rw [single_eq_smul_freeMk, map_smul, slicePres_a_app_freeMk]
        -- It remains: `r • (freeRank.map φ₀ v) = L_G (v ⊗ₜ r)`; prove by induction on `v`.
        exact smul_freeRank_map_eq_finsuppScalarLeft_tmul O X P.G r v
  -- **Identity B** (commuting square for `b`): the evaluated map `bₓ` intertwines
  -- with `rTensor P.π` across `eG, eP`.  Plan: reduce to generators `z = single i s`;
  -- LHS via `slicePres_b_app_freeMk` + `canonicalMap_tmul` (so `eP (s • F(g₀)(var i))
  -- = var i ⊗ s` after `comm`); RHS via `finsuppScalarLeft.symm` + `LinearMap.rTensor_tmul`
  -- + `P.toSolution.π (single i 1) = var i` (`Module.Relations.Solution.π_single`);
  -- both equal `(var i) ⊗ s`.
  have hIdB : ∀ z, eP ((slicePres_b O F V).app X z)
      = (LinearMap.rTensor (O.obj (Opposite.op Y) : Type r) P.toSolution.π) (eG z) := by
    intro z
    rw [heP, heG]
    simp only [LinearEquiv.coe_toEquiv, Equiv.trans_apply]
    induction z using Finsupp.induction_linear with
    | zero =>
        repeat (first | erw [LinearEquiv.map_zero] | erw [map_zero])
    | add p q hp hq =>
        simp only [map_add]
        rw [hp, hq]
    | single i r =>
        -- RHS: rewrite to the simple tensor `(var i) ⊗ₜ r`.
        conv_rhs => erw [finsuppScalarLeft_symm_apply_single]
        rw [LinearMap.rTensor_tmul, Module.Relations.Solution.π_single]
        -- LHS: `single i r = r • freeMk i`, pull `r` out, apply `slicePres_b_app_freeMk`.
        rw [single_eq_smul_freeMk, map_smul, slicePres_b_app_freeMk]
        -- Goal: `comm (c_g.symm (r • F(g₀)(var i))) = (var i) ⊗ₜ r`.
        -- Rewrite RHS as `comm (r ⊗ₜ var i)`, reduce to `c_g.symm (...) = r ⊗ₜ var i`.
        rw [← TensorProduct.comm_tmul (O.obj (Opposite.op V) : Type r)
            (O.obj (Opposite.op Y) : Type r) (F.obj (Opposite.op V) : Type r) r (P.var i)]
        congr 1
        -- `c_g.symm (r • F(g₀)(var i)) = r ⊗ₜ var i`, via `canonicalMap_tmul`.
        rw [LinearEquiv.symm_apply_eq]
        -- `(asIso c_g).toLinearEquiv (r ⊗ₜ var i) = c_g.hom (r ⊗ₜ var i) = r • F(g₀)(var i)`.
        show r • (show (F.obj (Opposite.op Y) : Type r) from
            F.map (X.unop.hom).op (P.var i))
          = (canonicalMap O F g₀).hom (r ⊗ₜ[(O.obj (Opposite.op V) : Type r)] (P.var i))
        rw [canonicalMap_tmul]
  constructor
  · -- The evaluated maps as plain functions.
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    -- It suffices to prove `Function.Exact aₓ bₓ`.
    suffices hExact : Function.Exact
        (fun z => (slicePres_a O F V).app X z)
        (fun z => (slicePres_b O F V).app X z) by
      exact (hExact x₂).mp hx₂
    refine exact_transport _ _ _ _ eR eG eP hIdA hIdB (fun p => ?_) hbc.1
    rw [heP]
    simp only [Equiv.trans_apply, LinearEquiv.coe_toEquiv]
    erw [LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff]
  · -- Reduce `Epi` to surjectivity of the evaluated `b` as a function.
    rw [PresheafOfModules.evaluation_map, ModuleCat.epi_iff_surjective]
    intro y
    -- `eP y` is surjected by `rTensor P.π` (base-change surjectivity).
    obtain ⟨w, hw⟩ := hbc.2 (eP y)
    -- pull `w` back to the evaluated free module via `eG.symm`.
    refine ⟨eG.symm w, ?_⟩
    apply eP.injective
    have hb := hIdB (eG.symm w)
    rw [Equiv.apply_symm_apply] at hb
    exact hb.trans hw

/-- **Objectwise exactness of the slice presentation.**  For every slice object
`X = (g : Y ⟶ V)`, the evaluated complex `⊕_J O(Y) → ⊕_I O(Y) → F(Y)` is exact. -/
theorem slicePres_objectwise_exact
    (h : ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso (canonicalMap O F f)) (V : C)
    (X : (Over V)ᵒᵖ) :
    ((ShortComplex.mk (slicePres_a O F V) (slicePres_b O F V) (slicePres_comp_zero O F V)).map
      (PresheafOfModules.evaluation ((Over.forget V).op ⋙ ringPresheaf O) X)).Exact :=
  (slicePres_objectwise_exact_and_epi O F h V X).1

/-- **Objectwise epimorphy of the slice presentation.**  For every slice object
`X = (g : Y ⟶ V)`, the evaluated `bₓ` is an epimorphism: surjectivity of the
base-changed `π` (`baseChange_presentation_exact`) survives composition with the
iso `c_g`. -/
theorem slicePres_objectwise_epi
    (h : ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso (canonicalMap O F f)) (V : C)
    (X : (Over V)ᵒᵖ) :
    Epi ((PresheafOfModules.evaluation ((Over.forget V).op ⋙ ringPresheaf O) X).map
      (slicePres_b O F V)) :=
  (slicePres_objectwise_exact_and_epi O F h V X).2

/-- If every canonical map `canonicalMap O F f` is an isomorphism, then for each `V : C` the
restriction `restrictToSlice O F V` admits a presentation `a ≫ b = 0` by free presheaves of
modules over `C/V` which is exact, with `b` an epimorphism, at every object of `C/V`. -/
theorem slicePresentation_data_of_isIso
    (h : ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso (canonicalMap O F f)) (V : C) :
    ∃ (I J : Type r)
      (a : freeRank ((Over.forget V).op ⋙ ringPresheaf O) J ⟶
            freeRank ((Over.forget V).op ⋙ ringPresheaf O) I)
      (b : freeRank ((Over.forget V).op ⋙ ringPresheaf O) I ⟶ restrictToSlice O F V)
      (w : a ≫ b = 0),
      (∀ X : (Over V)ᵒᵖ,
        ((ShortComplex.mk a b w).map
          (PresheafOfModules.evaluation ((Over.forget V).op ⋙ ringPresheaf O) X)).Exact) ∧
      (∀ X : (Over V)ᵒᵖ,
        Epi ((PresheafOfModules.evaluation ((Over.forget V).op ⋙ ringPresheaf O) X).map b)) :=
  ⟨(slicePres_P O F V).G, (slicePres_P O F V).R, slicePres_a O F V, slicePres_b O F V,
    slicePres_comp_zero O F V,
    slicePres_objectwise_exact O F h V,
    slicePres_objectwise_epi O F h V⟩

/-- (`⇐` direction of `0GZN`.)  If every canonical map `c_f` is an isomorphism,
then `F` is quasi-coherent.

**Argument.**  Fix `V : C`.  The `O(V)`-module `F(V)` admits *some* presentation
`⊕_J O(V) →(a₀) ⊕_I O(V) →(b₀) F(V) → 0` (every module is a cokernel of a map of
free modules; choose `I` a generating set and `J` a generating set of the kernel).
Promote `a₀, b₀` to maps of presheaves of `O|_{C/V}`-modules
`a : freeRank _ J ⟶ freeRank _ I`, `b : freeRank _ I ⟶ restrictToSlice O F V` by
the universal property of `freeRank` (a map out of `freeRank R K` is a `K`-indexed
family of global sections of the target) together with the slice-section
identification.  We must check that `⊕_J O|_{C/V} → ⊕_I O|_{C/V} →
restrictToSlice O F V → 0` is exact, i.e. exact objectwise.  At the object
`(f : U ⟶ V)` of `C/V`, evaluation gives (using objectwise sections of free
modules) the sequence `⊕_J O(U) → ⊕_I O(U) → F(U) → 0`.  But evaluating the chosen
`F(V)`-presentation and applying the right-exact functor `- ⊗_{O(V)} O(U)` gives
an exact `⊕_J O(U) → ⊕_I O(U) → F(V) ⊗_{O(V)} O(U) → 0`, and the hypothesis that
`c_f : F(V) ⊗_{O(V)} O(U) ≅ F(U)` is an isomorphism identifies the two sequences
(the cokernels agree via `c_f`, compatibly with the map from `⊕_I O(U)` because
`c_f (a ⊗ₜ s) = a • F(f)(s)`, `canonicalMap_tmul`).  Hence the slice sequence is
objectwise exact, so `restrictToSlice O F V` has a global presentation.  As `V`
was arbitrary, `F` is quasi-coherent. -/
theorem quasiCoherent_of_canonicalMap_isIso
    (h : ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso (canonicalMap O F f)) :
    QuasiCoherent O F := by
  -- Fix `V`; the goal `QuasiCoherent O F` unfolds to `∀ V, HasGlobalPresentation …`.
  intro V
  -- Extract the presentation data and the objectwise exactness / epi facts.
  obtain ⟨I, J, a, b, w, hexact, hepi⟩ := slicePresentation_data_of_isIso O F h V
  -- Assemble `HasGlobalPresentation`, lifting objectwise facts via the reflection lemmas.
  exact ⟨I, J, a, b, w, exact_of_evaluation _ _ hexact, epi_of_evaluation b hepi⟩

/-- (`⇒` direction of `0GZN`.)  If `F` is quasi-coherent, then every canonical
map `c_f` is an isomorphism.

**Argument.**  Let `f : U ⟶ V`.  Quasi-coherence at `V` gives a slice presentation
`⊕_J O|_{C/V} →(a) ⊕_I O|_{C/V} →(b) restrictToSlice O F V → 0` that is exact and
with `b` epi.  Evaluate sections at the two slice objects `(id_V : V ⟶ V)` and
`(f : U ⟶ V)`.  By objectwise exactness of sections together with the objectwise
formula for sections of free presheaves, evaluation at `id_V` yields an exact
sequence of `O(V)`-modules
  `⊕_J O(V) → ⊕_I O(V) → F(V) → 0`,                                       (P_V)
and evaluation at `f` yields an exact sequence of `O(U)`-modules
  `⊕_J O(U) → ⊕_I O(U) → F(U) → 0`,                                       (P_U)
with the *same* index sets `I, J`; moreover the comparison from (P_V) to (P_U) is
induced by the ring map `O(f) : O(V) → O(U)` (the slice restriction maps act on
free sections coordinatewise via `O(f)`, and on `F` via `F(f)`).  Now apply the
right-exact functor `- ⊗_{O(V)} O(U)` to (P_V): since `(⊕_K O(V)) ⊗_{O(V)} O(U) ≅
⊕_K O(U)` naturally, this produces an exact sequence
  `⊕_J O(U) → ⊕_I O(U) → F(V) ⊗_{O(V)} O(U) → 0`.                         (P_V ⊗)
The two right-exact sequences (P_U) and (P_V ⊗) have identical left two terms
`⊕_J O(U) → ⊕_I O(U)` (the maps agree because both are `O(f)` applied
coordinatewise to the matrix of `a`).  Hence their cokernels are canonically
isomorphic, and the resulting isomorphism `F(V) ⊗_{O(V)} O(U) ≅ F(U)` is exactly
`c_f`: it sends the class of `a ⊗ₜ s` (with `s` a section over `id_V` lifting an
element of `F(V)`) to `a • F(f)(s)`, by `canonicalMap_tmul`.  Therefore `c_f` is
an isomorphism. -/
theorem canonicalMap_isIso_of_quasiCoherent
    (h : QuasiCoherent O F) ⦃U V : C⦄ (f : U ⟶ V) :
    IsIso (canonicalMap O F f) := by
  classical
  obtain ⟨I, J, a, b, w, hSC, hb⟩ := h V
  -- slice objects and the slice morphism `ψ : Xv ⟶ Xu`
  set Xv : (Over V)ᵒᵖ := Opposite.op (Over.mk (𝟙 V)) with hXv
  set Xu : (Over V)ᵒᵖ := Opposite.op (Over.mk f) with hXu
  set ψ : Xv ⟶ Xu := (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 V)).op with hψ
  -- structure map of restrictToSlice along ψ is F.map f.op (defeq)
  have hstr : ∀ s : ((restrictToSlice O F V).obj Xv : Type r),
      ((restrictToSlice O F V).map ψ).hom s
        = (show (F.obj (Opposite.op U) : Type r) from
            F.map f.op (show (F.obj (Opposite.op V) : Type r) from s)) := fun s => rfl
  -- The algebra structure O(V) → O(U) via O(f).
  let : Algebra (O.obj (Opposite.op V) : Type r) (O.obj (Opposite.op U) : Type r) :=
    (ringRestriction O f).toAlgebra
  -- Exactness and surjectivity of the evaluated maps, from `hSC` and `hb`.
  have hex : ∀ Z, Function.Exact (a.app Z).hom (b.app Z).hom := fun Z =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hSC.map (PresheafOfModules.evaluation ((Over.forget V).op ⋙ ringPresheaf O) Z))
  have hsurj : ∀ Z, Function.Surjective (b.app Z).hom := fun Z =>
    (ModuleCat.epi_iff_surjective (b.app Z)).mp
      (inferInstanceAs (Epi ((PresheafOfModules.evaluation _ Z).map b)))
  -- Base change of the V-presentation along O(f).
  have hbc := baseChange_presentation_exact (R := (O.obj (Opposite.op V) : Type r))
    (S := (O.obj (Opposite.op U) : Type r)) (ringRestriction O f)
    (M := ((restrictToSlice O F V).obj Xv : Type r)) (a.app Xv).hom (b.app Xv).hom
    (hex Xv) (hsurj Xv)
  -- The finsupp/tensor identifications of the free sections at Xu.
  set eGU : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) I).obj Xu : Type r) ≃
      ((I →₀ (O.obj (Opposite.op V) : Type r)) ⊗[(O.obj (Opposite.op V) : Type r)]
        (O.obj (Opposite.op U) : Type r)) :=
    (finsuppScalarLeft (O.obj (Opposite.op V) : Type r) (O.obj (Opposite.op U) : Type r)
      I).symm.toEquiv with heGU
  set eRU : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) J).obj Xu : Type r) ≃
      ((J →₀ (O.obj (Opposite.op V) : Type r)) ⊗[(O.obj (Opposite.op V) : Type r)]
        (O.obj (Opposite.op U) : Type r)) :=
    (finsuppScalarLeft (O.obj (Opposite.op V) : Type r) (O.obj (Opposite.op U) : Type r)
      J).symm.toEquiv with heRU
  -- **Square A**: eGU (aU z) = rTensor aV (eRU z).
  have hSqA : ∀ z, eGU ((a.app Xu).hom z)
      = (LinearMap.rTensor (O.obj (Opposite.op U) : Type r) (a.app Xv).hom) (eRU z) := by
    intro z
    rw [heGU, heRU]
    simp only [LinearEquiv.coe_toEquiv]
    induction z using Finsupp.induction_linear with
    | zero => repeat (first | erw [LinearEquiv.map_zero] | erw [map_zero])
    | add p q hp hq =>
        simp only [map_add]
        rw [hp, hq]
    | single j c =>
        conv_rhs => erw [finsuppScalarLeft_symm_apply_single]
        rw [LinearMap.rTensor_tmul]
        rw [LinearEquiv.symm_apply_eq]
        -- LHS: single j c = c • freeMk j; naturality of a along ψ relates aU to aV.
        have hsr : (Finsupp.single j c
            : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) J).obj Xu : Type r))
            = c • (((freeRank ((Over.forget V).op ⋙ ringPresheaf O) J).map ψ).hom
                (ModuleCat.freeMk j)) := by
          rw [freeRank_map_freeMk,
            show (ModuleCat.freeMk j
              : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) J).obj Xu : Type r))
              = Finsupp.single j (1 : _) from rfl,
            Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hsr, map_smul]
        -- naturality of a along ψ: aU (map ψ x) = map ψ (aV x)
        rw [PresheafOfModules.naturality_apply a ψ]
        -- now have c • ((freeRank _ I).map ψ).hom ((a.app Xv).hom (freeMk j))
        -- RHS: L_I ((a.app Xv).hom (single j 1) ⊗ₜ c)
        exact smul_freeRank_map_eq_finsuppScalarLeft_tmul O Xu I c _
  -- The comparison map F(V) ⊗ O(U) → F(U) : x ↦ c_f (comm x).
  set cmpB : ((F.obj (Opposite.op V) : Type r) ⊗[(O.obj (Opposite.op V) : Type r)]
      (O.obj (Opposite.op U) : Type r)) → (F.obj (Opposite.op U) : Type r) :=
    fun x => (canonicalMap O F f).hom
      ((TensorProduct.comm (O.obj (Opposite.op V) : Type r) (F.obj (Opposite.op V) : Type r)
        (O.obj (Opposite.op U) : Type r)) x) with hcmpB
  -- **Square B**: bU z = cmpB (rTensor bV (eGU z)).
  have hSqB : ∀ z, (b.app Xu).hom z
      = cmpB ((LinearMap.rTensor (O.obj (Opposite.op U) : Type r) (b.app Xv).hom) (eGU z)) := by
    intro z
    rw [hcmpB, heGU]
    simp only [LinearEquiv.coe_toEquiv]
    induction z using Finsupp.induction_linear with
    | zero =>
        repeat (first | erw [LinearEquiv.map_zero] | erw [map_zero])
    | add p q hp hq =>
        simp only [map_add]
        rw [hp, hq]
    | single i c =>
        erw [finsuppScalarLeft_symm_apply_single]
        rw [LinearMap.rTensor_tmul]
        -- LHS: single i c = c • freeMk i; naturality of b along ψ + hstr.
        have hsr : (Finsupp.single i c
            : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) I).obj Xu : Type r))
            = c • (((freeRank ((Over.forget V).op ⋙ ringPresheaf O) I).map ψ).hom
                (ModuleCat.freeMk i)) := by
          rw [freeRank_map_freeMk,
            show (ModuleCat.freeMk i
              : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) I).obj Xu : Type r))
              = Finsupp.single i (1 : _) from rfl,
            Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hsr, map_smul, PresheafOfModules.naturality_apply b ψ, hstr]
        -- now LHS = c • F.map f.op ((b.app Xv).hom (freeMk i))
        -- RHS: c_f (comm ((b.app Xv).hom (single i 1) ⊗ₜ c))
        rw [show (ModuleCat.freeMk i
              : ((freeRank ((Over.forget V).op ⋙ ringPresheaf O) I).obj Xv : Type r))
              = Finsupp.single i (1 : _) from rfl]
        rw [TensorProduct.comm_tmul, canonicalMap_tmul]
        rfl
  -- The commutativity equivalence on tensors.
  set cm := TensorProduct.comm (O.obj (Opposite.op V) : Type r) (F.obj (Opposite.op V) : Type r)
    (O.obj (Opposite.op U) : Type r) with hcm
  -- `cmpB` is bijective.
  have hcmpB_surj : Function.Surjective cmpB := by
    intro t
    obtain ⟨z, hz⟩ := hsurj Xu t
    exact ⟨(LinearMap.rTensor (O.obj (Opposite.op U) : Type r) (b.app Xv).hom) (eGU z),
      by rw [← hSqB z, hz]⟩
  have hcmpB_ker : ∀ x, cmpB x = 0 → x = 0 := by
    intro x hx
    -- `rTensor bV` is surjective, write `x = rTensor bV y`.
    obtain ⟨y, hy⟩ := hbc.2 x
    -- `z := eGU.symm y`, so `eGU z = y`, `x = rTensor bV (eGU z)`.
    set z := eGU.symm y with hz
    have hxz : x = (LinearMap.rTensor (O.obj (Opposite.op U) : Type r) (b.app Xv).hom) (eGU z) := by
      rw [hz, Equiv.apply_symm_apply]
      exact hy.symm
    -- `cmpB x = bU z`, so `bU z = 0`.
    have hbz : (b.app Xu).hom z = 0 := by
      rw [hSqB z]
      exact hxz ▸ hx
    -- exactness at U: `z = aU z'`.
    obtain ⟨z', hz'⟩ := (hex Xu z).mp hbz
    -- then `x = rTensor bV (eGU (aU z')) = rTensor bV (rTensor aV (eRU z')) = 0`.
    rw [hxz, ← hz', hSqA z']
    exact (hbc.1 _).mpr ⟨eRU z', rfl⟩
  -- Conclude bijectivity of `canonicalMap`.
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  constructor
  · -- injective
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hcx : cmpB (cm.symm x) = 0 := by
      rw [hcmpB]
      simp only [hcm, LinearEquiv.apply_symm_apply]
      exact hx
    exact cm.symm.injective (a₂ := 0) (by rw [hcmpB_ker _ hcx]; simp)
  · -- surjective
    intro t
    obtain ⟨y, hy⟩ := hcmpB_surj t
    refine ⟨cm y, ?_⟩
    rw [hcmpB] at hy
    simpa using hy

/-- Stacks Tag `0GZN`, Lemma 18.24.3: A sheaf of `O`-modules `F` on the chaotic
site `C` is quasi-coherent if and only if for every morphism `f : U ⟶ V` of `C`
the canonical map `c_f : F(V) ⊗_{O(V)} O(U) ⟶ F(U)` is an isomorphism. -/
@[stacks 0GZN]
theorem quasiCoherent_iff_canonicalMap_isIso :
    QuasiCoherent O F ↔ ∀ ⦃U V : C⦄ (f : U ⟶ V), IsIso (canonicalMap O F f) :=
  ⟨fun h _ _ f => canonicalMap_isIso_of_quasiCoherent O F h f,
    fun h => quasiCoherent_of_canonicalMap_isIso O F h⟩

end ChaoticQCoh
