module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kernels, coimages and single-degree placement of filtered objects

## The kernel and the coimage of a morphism of filtered objects

For a morphism `d : Y ⟶ Y'` of filtered objects of an abelian category, the kernel and the coimage
of `d` as filtered objects, the short exact sequence `0 → Ker(d) → Y → Coim(d) → 0` of graded
pieces they sit in, and, for a second morphism `d' : Y' ⟶ Y''` with vanishing composite, the map
`Coim(d) ⟶ Ker(d')` through which `d` factors. These are the data the Cartan–Eilenberg resolution
of [Stacks, Tag 05TW] takes from `Fil^f(𝒜)`: it resolves the terms of the sequences
`0 → Ker(d_K^i) → K^i → Coim(d_K^i) → 0` attached to a filtered complex `K^•` and lifts the maps
`u_i : Coim(d_K^i) ⟶ Ker(d_K^{i + 1})` to the chosen resolutions.

`Ker(d)` is filtered by `F^p Ker(d) = Ker(d) ∩ F^p Y`, realised as the kernel of `d` on the `p`-th
steps rather than as the pullback of `F^p Y ⟶ Y` along `Ker(d) ⟶ Y`. The two agree because
`F^p Y' ⟶ Y'` is a monomorphism, and in this form the steps are again kernels, so their inclusions
into `Ker(d)` are `kernel.map`s, which makes their monomorphy and their invertibility where the
filtration of `Y` is exhausted instances already available. `Coim(d) = Y/Ker(d)` carries the
quotient filtration, which is `cokernelObj` of the strict monomorphism `Ker(d) ⟶ Y`.

The two spellings of a filtration step — `F^i Ker(d)` as `(kernelFil d).filtration.obj i` and as
`kernel (d.natTrans.app i)` — agree only by unfolding `MonoOver.mk`, so the lifts and descents
below are named in the filtered spelling and the proofs stay inside it.

## Filtered objects placed in a single degree

[Stacks, Tag 05TT] and [Stacks, Tag 05TV] are stated for filtered complexes concentrated in degree
`0`, so their consumers need the passage from a filtered object `A` of `𝒜` to the filtered complex
`A[j]`, which is `A` in degree `j` and zero elsewhere, filtered by the subcomplexes `(F^p A)[j]`.
That is the functor `singleFil j`; the steps are subcomplexes because `HomologicalComplex.single`
preserves monomorphisms, and on the complexes concentrated in degree `j` the functor is inverse to
`evalFil (·) j`.

Placing in a degree commutes with `gr^p` (`gradedPieceSingleFilIso`), that functor preserving the
cokernel which defines `gr^p`. Hence short exactness of the graded pieces of `0 → A → B → C → 0`
transfers to `0 → A[j] → B[j] → C[j] → 0` (`shortExact_gradedPiece_singleFil_map`), which is the
hypothesis [Stacks, Tag 05TV] takes, and a finite filtration of `A` gives the degreewise finite
filtration of `A[j]` that [Stacks, Tag 05TT] and [Stacks, Tag 05TV] take
(`isDegreewiseFinite_singleFil`).

## What the termwise splitting of [Stacks, Tag 05TV] gives

[Stacks, Tag 05TV] produces a short exact sequence `0 → I^• → M^• → J^• → 0` of filtered complexes
split in each degree `n` by a retraction `r` of `u^n` and a section `s` of `v^n` compatible with
the filtrations, together with a morphism `b : B[0] ⟶ M^•`. Four further properties of its output
are what a Cartan–Eilenberg resolution needs of `M^•`: that `M^•` vanishes in negative degrees,
that each `M^n` has finite filtration, that each `gr^p(M^n)` is an injective object of `𝒜`, and
that `b` is a filtered quasi-isomorphism.

All four follow from the splitting. Call a retraction `r` and a section `s` *complementary* when
`r ≫ u + v ≫ s = 𝟙`; the pair the source produces need not be, but `r - v ≫ s ≫ r` is complementary
to `s`, because the retraction complementary to a section is unique and exactness makes it a
retraction. The filtration steps inherit the same correction, their structure maps into `M^n` being
monomorphisms, so `M^n` is the biproduct of `I^n` and `J^n` and `F^p M^n` that of `F^p I^n` and
`F^p J^n`: whence the vanishing and the finiteness. The two retractions assemble into a morphism of
filtered objects, so `gr^p` of the sequence in degree `n` is split as well: whence the injectivity
and, degreewise splitness being short exactness, the short exact sequence
`0 → gr^p I^• → gr^p M^• → gr^p J^• → 0`, to which two out of three for quasi-isomorphisms in the
middle applies.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section KernelCoimage

open CochainComplex.FilteredInjective.Resolution

namespace CategoryTheory.FilteredObject

variable {Y Y' Y'' Z T : FilteredObject 𝒜 ℤᵒᵖ}

/-! #### The kernel -/

/-- The `i`-th step of the induced filtration on the kernel of a morphism `d : Y ⟶ Y'` of filtered
objects: the kernel of `d` on the `i`-th steps, included in `Ker(d)` by the map the inclusions
`F^i Y ⟶ Y`, `F^i Y' ⟶ Y'` induce on kernels. It is the intersection `Ker(d) ∩ F^i Y`, a map into
`F^i Y` being killed by `d` exactly when it is killed by `d` on the `i`-th steps. -/
@[implicit_reducible]
public noncomputable def kernelFilStep (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    kernel (d.natTrans.app i) ⟶ kernel d.hom :=
  kernel.map _ _ (Y.filtration.ι.app i) (Y'.filtration.ι.app i) (d.comm i)

/-- The step `F^i Ker(d) ⟶ Ker(d)` sits over `F^i Y ⟶ Y`. -/
@[reassoc]
public lemma kernelFilStep_comp_ι (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    kernelFilStep d i ≫ kernel.ι d.hom =
      kernel.ι (d.natTrans.app i) ≫ Y.filtration.ι.app i :=
  kernel.lift_ι ..

/-- The steps of the induced filtration are subobjects of `Ker(d)`: each factors the monomorphism
`F^i Ker(d) ⟶ F^i Y ⟶ Y`. -/
public instance mono_kernelFilStep (d : Y ⟶ Y') (i : ℤᵒᵖ) : Mono (kernelFilStep d i) :=
  mono_of_mono_fac (kernelFilStep_comp_ι d i)

/-- Where the filtration of `Y` is exhausted, so is the induced filtration of `Ker(d)`. -/
public lemma isIso_kernelFilStep (d : Y ⟶ Y') {i : ℤᵒᵖ} (hi : IsIso (Y.filtration.ι.app i)) :
    IsIso (kernelFilStep d i) := by
  have := hi
  exact inferInstanceAs
    (IsIso (kernel.map _ _ (Y.filtration.ι.app i) (Y'.filtration.ι.app i) (d.comm i)))

/-- The steps of the induced filtration on `Ker(d)` are compatible with the inclusions of the
filtration of `Y`. -/
public lemma kernelFilStep_naturality (d : Y ⟶ Y') {i j : ℤᵒᵖ} (f : i ⟶ j) :
    kernel.map _ _ (Y.filtration.diagram.map f) (Y'.filtration.diagram.map f)
        (d.natTrans.naturality f).symm ≫ kernelFilStep d j = kernelFilStep d i := by
  refine (cancel_mono (kernel.ι d.hom)).1 ?_
  rw [Category.assoc, kernelFilStep_comp_ι, kernelFilStep_comp_ι, ← Category.assoc,
    kernel.lift_ι, Category.assoc, Filtration.diagram_map_comp_ι_app]

/-- The induced filtration `F^i Ker(d) = Ker(d) ∩ F^i Y` of the kernel of `d`, functorially in
`i`. -/
@[implicit_reducible]
public noncomputable def kernelFiltration (d : Y ⟶ Y') : ℤᵒᵖ ⥤ MonoOver (kernel d.hom) where
  obj i := MonoOver.mk (kernelFilStep d i)
  map f := MonoOver.homMk
    (kernel.map _ _ (Y.filtration.diagram.map f) (Y'.filtration.diagram.map f)
      (d.natTrans.naturality f).symm) (kernelFilStep_naturality d f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The kernel of a morphism `d : Y ⟶ Y'` of filtered objects, as a filtered object: `Ker(d)` in
`𝒜` with the induced filtration `F^p Ker(d) = Ker(d) ∩ F^p Y`. -/
@[implicit_reducible]
public noncomputable def kernelFil (d : Y ⟶ Y') : FilteredObject 𝒜 ℤᵒᵖ where
  X := kernel d.hom
  filtration := ⟨kernelFiltration d⟩

/-- The underlying object of `kernelFil d` is `kernel d.hom`. -/
public lemma kernelFil_X (d : Y ⟶ Y') : (kernelFil d).X = kernel d.hom := rfl

/-- The `i`-th filtration step of `kernelFil d` is the kernel of `d` on the `i`-th steps. -/
public lemma kernelFil_filtration_obj (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    (kernelFil d).filtration.obj i = kernel (d.natTrans.app i) := rfl

/-- The inclusion of the `i`-th filtration step of `kernelFil d` is `kernelFilStep d i`. -/
public lemma kernelFil_filtration_ι_app (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    (kernelFil d).filtration.ι.app i = kernelFilStep d i := rfl

/-- The inclusion `Ker(d) ⟶ Y`, as a morphism of filtered objects for the induced filtration. -/
@[implicit_reducible]
public noncomputable def kernelFilι (d : Y ⟶ Y') : kernelFil d ⟶ Y :=
  FilteredObject.homMk (kernel.ι d.hom) (fun i => kernel.ι (d.natTrans.app i))
    (fun i => (kernelFilStep_comp_ι d i).symm)

/-- On underlying objects, `kernelFilι d` is `kernel.ι d.hom`. -/
public lemma kernelFilι_hom (d : Y ⟶ Y') : (kernelFilι d).hom = kernel.ι d.hom := rfl

/-- On the `i`-th steps, `kernelFilι d` is the kernel inclusion of `d.natTrans.app i`. -/
public lemma kernelFilι_natTrans_app (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    (kernelFilι d).natTrans.app i = kernel.ι (d.natTrans.app i) := rfl

/-- The inclusion `Ker(d) ⟶ Y` is a monomorphism on underlying objects. -/
public instance mono_kernelFilι_hom (d : Y ⟶ Y') : Mono (kernelFilι d).hom :=
  inferInstanceAs (Mono (kernel.ι d.hom))

/-- The inclusion `Ker(d) ⟶ Y` is a monomorphism on every filtration step. -/
public instance mono_kernelFilι_natTrans_app (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    Mono ((kernelFilι d).natTrans.app i) :=
  mono_of_mono_fac ((kernelFilι d).comm i)

/-- `Ker(d) ⟶ Y ⟶ Y'` vanishes, read on the underlying objects; `natTrans_app_eq_zero` then gives
the vanishing on each filtration step. -/
public lemma kernelFilι_comp_hom (d : Y ⟶ Y') : (kernelFilι d ≫ d).hom = 0 :=
  kernel.condition d.hom

/-- A map into `F^i Y` killed by `d` on the `i`-th steps factors through `F^i Ker(d)`. -/
public noncomputable def kernelFilStepLift (d : Y ⟶ Y') (i : ℤᵒᵖ) {W : 𝒜}
    (a : W ⟶ Y.filtration.obj i) (ha : a ≫ d.natTrans.app i = 0) :
    W ⟶ (kernelFil d).filtration.obj i :=
  kernel.lift (d.natTrans.app i) a ha

/-- The lift `kernelFilStepLift d i a ha` followed by `F^i Ker(d) ⟶ F^i Y` is `a`. -/
@[reassoc]
public lemma kernelFilStepLift_comp_natTrans_app (d : Y ⟶ Y') (i : ℤᵒᵖ) {W : 𝒜}
    (a : W ⟶ Y.filtration.obj i) (ha : a ≫ d.natTrans.app i = 0) :
    kernelFilStepLift d i a ha ≫ (kernelFilι d).natTrans.app i = a :=
  kernel.lift_ι ..

/-- The inclusion `Ker(d) ⟶ Y` is strict: the induced filtration is the preimage under `Ker(d) ⟶ Y`
of the filtration of `Y`, a map into `F^i Y` landing in `Ker(d)` being killed by `d` on the `i`-th
steps. -/
public instance isStrictHom_kernelFilι (d : Y ⟶ Y') : IsStrictHom (kernelFilι d) := by
  constructor
  intro i
  have key : ∀ s : PullbackCone (Y.filtration.ι.app i) (kernelFilι d).hom,
      s.fst ≫ d.natTrans.app i = 0 := fun s => by
    refine zero_of_comp_mono (Y'.filtration.ι.app i) ?_
    rw [Category.assoc, d.comm i, ← Category.assoc, s.condition, Category.assoc,
      show (kernelFilι d).hom ≫ d.hom = 0 from kernelFilι_comp_hom d, comp_zero]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ((kernelFilι d).comm i)
    (fun s => kernelFilStepLift d i s.fst (key s))
    (fun s => kernelFilStepLift_comp_natTrans_app ..) (fun s => ?_) (fun s m h₁ _ => ?_))
  · refine (cancel_mono (kernelFilι d).hom).1 ?_
    rw [Category.assoc, ← (kernelFilι d).comm i, ← Category.assoc,
      kernelFilStepLift_comp_natTrans_app, s.condition]
  · refine (cancel_mono ((kernelFilι d).natTrans.app i)).1 ?_
    rw [kernelFilStepLift_comp_natTrans_app, h₁]

/-- Two morphisms into `Ker(d)` agreeing after `Ker(d) ⟶ Y` are equal. -/
public lemma kernelFil_hom_ext (d : Y ⟶ Y') {s s' : Z ⟶ kernelFil d}
    (h : s ≫ kernelFilι d = s' ≫ kernelFilι d) : s = s' := by
  refine FilteredObject.hom_ext ((cancel_mono (kernelFilι d).hom).1 ?_)
  rw [← FilteredObject.comp_hom, ← FilteredObject.comp_hom, h]

/-- A morphism `t : Z ⟶ Y` of filtered objects killed by `d` factors through `Ker(d)`. -/
public noncomputable def kernelFilLift (d : Y ⟶ Y') (t : Z ⟶ Y) (ht : (t ≫ d).hom = 0) :
    Z ⟶ kernelFil d :=
  FilteredObject.homMk (kernel.lift d.hom t.hom ht)
    (fun i => kernelFilStepLift d i (t.natTrans.app i)
      (natTrans_app_eq_zero (t ≫ d) ht i))
    (fun i => by
      refine (cancel_mono (kernelFilι d).hom).1 ?_
      rw [Category.assoc, ← (kernelFilι d).comm i, ← Category.assoc,
        kernelFilStepLift_comp_natTrans_app, t.comm i, Category.assoc, kernelFilι_hom,
        kernel.lift_ι])

/-- The lift `kernelFilLift d t ht` followed by `Ker(d) ⟶ Y` is `t`. -/
public lemma kernelFilLift_comp_kernelFilι (d : Y ⟶ Y') (t : Z ⟶ Y) (ht : (t ≫ d).hom = 0) :
    kernelFilLift d t ht ≫ kernelFilι d = t :=
  FilteredObject.hom_ext (kernel.lift_ι ..)

/-- **The universal property of `Ker(d)` in `Fil(𝒜)`.** A morphism `t : Z ⟶ Y` of filtered objects
whose composite with `d` vanishes factors uniquely through the inclusion `Ker(d) ⟶ Y`. -/
public theorem existsUnique_comp_kernelFilι (d : Y ⟶ Y') (t : Z ⟶ Y) (ht : (t ≫ d).hom = 0) :
    ∃! s : Z ⟶ kernelFil d, s ≫ kernelFilι d = t :=
  ⟨kernelFilLift d t ht, kernelFilLift_comp_kernelFilι d t ht, fun s hs =>
    kernelFil_hom_ext d (by rw [hs, kernelFilLift_comp_kernelFilι])⟩

/-- The induced filtration of `Ker(d)` is finite as soon as the filtration of `Y` is: it is
exhausted where that of `Y` is, and it vanishes where that of `Y` does, `F^q Ker(d)` being a
subobject of `F^q Y`. This is the finiteness hypothesis [Stacks, Tag 05TT] and [Stacks, Tag 05TV]
take on a filtered object; for a filtered complex they ask it of each degree separately. -/
public lemma kernelFil_filtration_isFinite (d : Y ⟶ Y') (hY : Y.filtration.IsFinite) :
    (kernelFil d).filtration.IsFinite := by
  refine .of_exists ?_ ?_
  · obtain ⟨p, hp⟩ := hY.exists_isIso_ι
    exact ⟨p, isIso_kernelFilStep d hp⟩
  · obtain ⟨q, hq⟩ := hY.exists_isZero_obj
    exact ⟨q, IsZero.of_mono ((kernelFilι d).natTrans.app (op q)) hq⟩

/-! #### The coimage -/

/-- The coimage of a morphism `d : Y ⟶ Y'` of filtered objects, as a filtered object: the quotient
`Coim(d) = Y/Ker(d)` in `𝒜` with the quotient filtration `F^p Coim(d) = F^p Y / F^p Ker(d)`. The
inclusion `Ker(d) ⟶ Y` being strict is what makes those quotients subobjects of `Coim(d)`. -/
@[implicit_reducible]
public noncomputable def coimageFil (d : Y ⟶ Y') : FilteredObject 𝒜 ℤᵒᵖ :=
  CochainComplex.FilteredInjective.Resolution.cokernelObj (kernelFilι d)

/-- The underlying object of `coimageFil d` is the cokernel of `Ker(d) ⟶ Y`. -/
public lemma coimageFil_X (d : Y ⟶ Y') : (coimageFil d).X = cokernel (kernelFilι d).hom := rfl

/-- The `i`-th filtration step of `coimageFil d` is the cokernel of `F^i Ker(d) ⟶ F^i Y`. -/
public lemma coimageFil_filtration_obj (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    (coimageFil d).filtration.obj i = cokernel ((kernelFilι d).natTrans.app i) := rfl

/-- The inclusion of the `i`-th filtration step of `coimageFil d` is
`cokernelStep (kernelFilι d) i`. -/
public lemma coimageFil_filtration_ι_app (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    (coimageFil d).filtration.ι.app i = cokernelStep (kernelFilι d) i := rfl

/-- The projection `Y ⟶ Coim(d)`. It is surjective on the underlying objects and on every
filtration step, which is the strictness of a filtered epimorphism. The pullback condition
`FilteredObject.IsStrictHom` is a different statement and fails here: the preimage of
`F^p Coim(d)` is `F^p Y + Ker(d)`, so for `Y = ℤ` filtered by `F^0 Y = ℤ`, `F^1 Y = 0` and `d = 0`
the square at `p = 1` has `F^1 Y = 0` where the pullback is `Y`. -/
@[implicit_reducible]
public noncomputable def coimageFilπ (d : Y ⟶ Y') : Y ⟶ coimageFil d :=
  CochainComplex.FilteredInjective.Resolution.cokernelπ (kernelFilι d)

/-- On underlying objects, `coimageFilπ d` is the cokernel projection of `Ker(d) ⟶ Y`. -/
public lemma coimageFilπ_hom (d : Y ⟶ Y') :
    (coimageFilπ d).hom = cokernel.π (kernelFilι d).hom := rfl

/-- On the `i`-th filtration steps, `coimageFilπ d` is the cokernel projection of
`F^i Ker(d) ⟶ F^i Y`. -/
public lemma coimageFilπ_natTrans_app (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    (coimageFilπ d).natTrans.app i = cokernel.π ((kernelFilι d).natTrans.app i) := rfl

/-- The projection `Y ⟶ Coim(d)` is an epimorphism on underlying objects. -/
public instance epi_coimageFilπ_hom (d : Y ⟶ Y') : Epi (coimageFilπ d).hom :=
  inferInstanceAs (Epi (cokernel.π (kernelFilι d).hom))

/-- The projection `Y ⟶ Coim(d)` is an epimorphism on every filtration step. -/
public instance epi_coimageFilπ_natTrans_app (d : Y ⟶ Y') (i : ℤᵒᵖ) :
    Epi ((coimageFilπ d).natTrans.app i) :=
  inferInstanceAs (Epi (cokernel.π ((kernelFilι d).natTrans.app i)))

/-- A map out of `F^i Y` killing `F^i Ker(d)` descends to `F^i Coim(d)`. -/
public noncomputable def coimageFilStepDesc (d : Y ⟶ Y') (i : ℤᵒᵖ) {W : 𝒜}
    (a : Y.filtration.obj i ⟶ W) (ha : (kernelFilι d).natTrans.app i ≫ a = 0) :
    (coimageFil d).filtration.obj i ⟶ W :=
  cokernel.desc ((kernelFilι d).natTrans.app i) a ha

/-- `F^i Y ⟶ F^i Coim(d)` followed by the descent `coimageFilStepDesc d i a ha` is `a`. -/
@[reassoc]
public lemma natTrans_app_comp_coimageFilStepDesc (d : Y ⟶ Y') (i : ℤᵒᵖ) {W : 𝒜}
    (a : Y.filtration.obj i ⟶ W) (ha : (kernelFilι d).natTrans.app i ≫ a = 0) :
    (coimageFilπ d).natTrans.app i ≫ coimageFilStepDesc d i a ha = a :=
  cokernel.π_desc ..

/-- A map out of `Y` killing `Ker(d)` descends to `Coim(d)`, on the underlying objects. -/
public noncomputable def coimageFilDescHom (d : Y ⟶ Y') {W : 𝒜} (a : Y.X ⟶ W)
    (ha : (kernelFilι d).hom ≫ a = 0) : (coimageFil d).X ⟶ W :=
  cokernel.desc (kernelFilι d).hom a ha

/-- `Y ⟶ Coim(d)` followed by the descent `coimageFilDescHom d a ha` is `a`. -/
@[reassoc]
public lemma hom_comp_coimageFilDescHom (d : Y ⟶ Y') {W : 𝒜} (a : Y.X ⟶ W)
    (ha : (kernelFilι d).hom ≫ a = 0) :
    (coimageFilπ d).hom ≫ coimageFilDescHom d a ha = a :=
  cokernel.π_desc ..

/-- Two morphisms out of `Coim(d)` agreeing after `Y ⟶ Coim(d)` are equal. -/
public lemma coimageFil_hom_ext (d : Y ⟶ Y') {s s' : coimageFil d ⟶ T}
    (h : coimageFilπ d ≫ s = coimageFilπ d ≫ s') : s = s' := by
  refine FilteredObject.hom_ext ((cancel_epi (coimageFilπ d).hom).1 ?_)
  rw [← FilteredObject.comp_hom, ← FilteredObject.comp_hom, h]

/-- **The universal property of `Coim(d)` in `Fil(𝒜)`.** A morphism `t : Y ⟶ T` of filtered objects
killing `Ker(d) ⟶ Y` descends to `Coim(d)`. -/
public noncomputable def coimageFilDesc (d : Y ⟶ Y') (t : Y ⟶ T)
    (ht : (kernelFilι d ≫ t).hom = 0) : coimageFil d ⟶ T :=
  FilteredObject.homMk (coimageFilDescHom d t.hom ht)
    (fun i => coimageFilStepDesc d i (t.natTrans.app i)
      (natTrans_app_eq_zero (kernelFilι d ≫ t) ht i))
    (fun i => by
      refine (cancel_epi ((coimageFilπ d).natTrans.app i)).1 ?_
      rw [natTrans_app_comp_coimageFilStepDesc_assoc, ← Category.assoc,
        (coimageFilπ d).comm i, Category.assoc, hom_comp_coimageFilDescHom, t.comm i])

/-- The projection `Y ⟶ Coim(d)` followed by the descent `coimageFilDesc d t ht` is `t`. -/
public lemma coimageFilπ_comp_coimageFilDesc (d : Y ⟶ Y') (t : Y ⟶ T)
    (ht : (kernelFilι d ≫ t).hom = 0) : coimageFilπ d ≫ coimageFilDesc d t ht = t :=
  FilteredObject.hom_ext (hom_comp_coimageFilDescHom ..)

/-- The inclusion `Coim(d) ⟶ Y'` of the coimage. -/
public noncomputable def coimageFilι (d : Y ⟶ Y') : coimageFil d ⟶ Y' :=
  coimageFilDesc d d (kernelFilι_comp_hom d)

/-- The factorisation `Y ⟶ Coim(d) ⟶ Y'` of `d` through its coimage. -/
public lemma coimageFilπ_comp_coimageFilι (d : Y ⟶ Y') :
    coimageFilπ d ≫ coimageFilι d = d :=
  coimageFilπ_comp_coimageFilDesc d d (kernelFilι_comp_hom d)

/-- The quotient filtration of `Coim(d)` is finite as soon as the filtration of `Y` is. -/
public lemma coimageFil_filtration_isFinite (d : Y ⟶ Y') (hY : Y.filtration.IsFinite) :
    (coimageFil d).filtration.IsFinite :=
  cokernelObj_filtration_isFinite (kernelFilι d) hY

/-! #### Exactness on the graded pieces -/

/-- The composite `gr^p Ker(d) ⟶ gr^p Y ⟶ gr^p Coim(d)` vanishes. -/
public lemma gradedPiece_map_kernelFilι_comp_coimageFilπ (d : Y ⟶ Y') (p : ℤ) :
    (gr p).map (kernelFilι d) ≫ (gr p).map (coimageFilπ d) = 0 :=
  gradedPiece_map_comp_cokernelπ (kernelFilι d) p

/-- **The short exact sequence `0 → Ker(d) → Y → Coim(d) → 0` of `Fil(𝒜)`**, in the form
[Stacks, Tag 05TV] consumes it: for every `p` the sequence
`0 → gr^p Ker(d) → gr^p Y → gr^p Coim(d) → 0` of graded pieces is short exact. This is
[Stacks, Tag 0127] for the strict monomorphism `Ker(d) ⟶ Y`. -/
@[ega "IV 19.6.1" "more general"]
public lemma shortExact_gradedPiece_kernelFilι_coimageFilπ (d : Y ⟶ Y') (p : ℤ) :
    (ShortComplex.mk _ _ (gradedPiece_map_kernelFilι_comp_coimageFilπ d p)).ShortExact :=
  shortExact_gradedPiece_cokernelπ (kernelFilι d) p _

/-! #### The connecting map -/

/-- **The map `Coim(d) ⟶ Ker(d')`** attached to two composable morphisms of filtered objects with
vanishing composite: `d` lands in `Ker(d')` by the universal property of the kernel, and the
resulting map kills `Ker(d) ⟶ Y`, hence descends to the coimage. For the differential of a
filtered complex this is the map `u_i : Coim(d_K^i) ⟶ Ker(d_K^{i + 1})` of [Stacks, Tag 05TW]. -/
public noncomputable def coimageToKernelFil (d : Y ⟶ Y') (d' : Y' ⟶ Y'')
    (h : (d ≫ d').hom = 0) : coimageFil d ⟶ kernelFil d' :=
  coimageFilDesc d (kernelFilLift d' d h)
    (by
      refine zero_of_comp_mono (kernelFilι d').hom ?_
      rw [FilteredObject.comp_hom, Category.assoc, ← FilteredObject.comp_hom,
        kernelFilLift_comp_kernelFilι, ← FilteredObject.comp_hom]
      exact kernelFilι_comp_hom d)

/-- The map `Coim(d) ⟶ Ker(d')` factors `d`: `Y ⟶ Coim(d) ⟶ Ker(d') ⟶ Y'` is `d`. -/
public lemma coimageFilπ_comp_coimageToKernelFil_comp_kernelFilι (d : Y ⟶ Y') (d' : Y' ⟶ Y'')
    (h : (d ≫ d').hom = 0) :
    coimageFilπ d ≫ coimageToKernelFil d d' h ≫ kernelFilι d' = d := by
  have hπ : coimageFilπ d ≫ coimageToKernelFil d d' h = kernelFilLift d' d h :=
    coimageFilπ_comp_coimageFilDesc d _ _
  rw [← Category.assoc, hπ, kernelFilLift_comp_kernelFilι]

open CochainComplex.FilteredInjective.TermwiseSplit in
/-- The connecting map `u_i : Coim(d_K^i) ⟶ Ker(d_K^{i + 1})` of a filtered complex `K^•`, the map
[Stacks, Tag 05TW] lifts to the filtered injective resolutions of the terms of `K^•`. -/
public noncomputable def coimKer (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (i : ℤ) :
    coimageFil (evalD K i) ⟶ kernelFil (evalD K (i + 1)) :=
  coimageToKernelFil _ _ (K.X.d_comp_d i (i + 1) (i + 1 + 1))

open CochainComplex.FilteredInjective.TermwiseSplit in
/-- The connecting map factors the differential: `K^i ⟶ Coim(d^i) ⟶ Ker(d^{i + 1}) ⟶ K^{i + 1}` is
`d^i`. -/
public lemma coimageFilπ_comp_coimKer_comp_kernelFilι
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (i : ℤ) :
    coimageFilπ (evalD K i) ≫ coimKer K i ≫ kernelFilι (evalD K (i + 1)) = evalD K i :=
  coimageFilπ_comp_coimageToKernelFil_comp_kernelFilι _ _ _

end CategoryTheory.FilteredObject

end KernelCoimage

section SingleDegree

namespace CategoryTheory.FilteredObject

/-- The functor `Fil(𝒜) ⥤ Fil(CochainComplex 𝒜 ℤ)` placing a filtered object `A` in degree `j`:
the complex `A[j]`, which is `A` in degree `j` and zero elsewhere, filtered by the subcomplexes
`(F^p A)[j]`. -/
@[implicit_reducible]
public noncomputable def singleFil (j : ℤ) :
    FilteredObject 𝒜 ℤᵒᵖ ⥤ FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  obj A :=
    { X := (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).obj A.X
      filtration := ⟨A.filtration.toMonoOver ⋙ MonoOver.lift
        (Over.post (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j))
        (fun f => by have := f.2; dsimp [Over.post]; infer_instance)⟩ }
  map {A B} f := FilteredObject.homMk
      ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map f.hom)
      (fun i => (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map (f.natTrans.app i))
      (fun i =>
        ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map_comp (f.natTrans.app i)
            (B.filtration.ι.app i)).symm.trans
          ((congrArg (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map (f.comm i)).trans
            ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map_comp
              (A.filtration.ι.app i) f.hom)))
  map_id A :=
    FilteredObject.hom_ext ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map_id A.X)
  map_comp f g :=
    FilteredObject.hom_ext
      ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map_comp f.hom g.hom)

/-- The underlying complex of `A[j]` is `A` placed in degree `j`. -/
public lemma singleFil_obj_X (j : ℤ) (A : FilteredObject 𝒜 ℤᵒᵖ) :
    ((singleFil j).obj A).X = (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).obj A.X :=
  rfl

/-- The `i`-th filtration step of `A[j]` is `F^i A` placed in degree `j`. -/
@[simp]
public lemma singleFil_filtration_obj (j : ℤ) (A : FilteredObject 𝒜 ℤᵒᵖ) (i : ℤᵒᵖ) :
    ((singleFil j).obj A).filtration.obj i =
      (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).obj (A.filtration.obj i) :=
  rfl

/-- The inclusion of the `i`-th step of `A[j]` is that of `F^i A` placed in degree `j`. -/
@[simp]
public lemma singleFil_filtration_ι_app (j : ℤ) (A : FilteredObject 𝒜 ℤᵒᵖ) (i : ℤᵒᵖ) :
    ((singleFil j).obj A).filtration.ι.app i =
      (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map (A.filtration.ι.app i) :=
  rfl

/-- The transition maps of the filtration of `A[j]` are those of `A` placed in degree `j`. -/
@[simp]
public lemma singleFil_filtration_diagram_map (j : ℤ) (A : FilteredObject 𝒜 ℤᵒᵖ) {i i' : ℤᵒᵖ}
    (φ : i ⟶ i') :
    ((singleFil j).obj A).filtration.diagram.map φ =
      (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map (A.filtration.diagram.map φ) :=
  rfl

/-- On underlying complexes, `singleFil j` sends `f` to `f` placed in degree `j`. -/
@[simp]
public lemma singleFil_map_hom {A B : FilteredObject 𝒜 ℤᵒᵖ} (j : ℤ) (f : A ⟶ B) :
    ((singleFil j).map f).hom = (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map f.hom :=
  rfl

/-- On the `i`-th filtration steps, `singleFil j` sends `f` to its `i`-th step placed in degree
`j`. -/
@[simp]
public lemma singleFil_map_natTrans_app {A B : FilteredObject 𝒜 ℤᵒᵖ} (j : ℤ) (f : A ⟶ B)
    (i : ℤᵒᵖ) :
    ((singleFil j).map f).natTrans.app i =
      (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map (f.natTrans.app i) :=
  rfl

/-- The complex underlying `A[j]` is strictly concentrated in degrees `≥ j`. -/
public instance isStrictlyGE_singleFil (j : ℤ) (A : FilteredObject 𝒜 ℤᵒᵖ) :
    ((singleFil j).obj A).X.IsStrictlyGE j := by
  rw [singleFil_obj_X]
  infer_instance

/-- The complex underlying `A[j]` is strictly concentrated in degrees `≤ j`. -/
public instance isStrictlyLE_singleFil (j : ℤ) (A : FilteredObject 𝒜 ℤᵒᵖ) :
    ((singleFil j).obj A).X.IsStrictlyLE j := by
  rw [singleFil_obj_X]
  infer_instance

/-- **The graded pieces of a filtered object placed in a degree**: `gr^p(A[j]) ≅ (gr^p A)[j]`,
as `HomologicalComplex.single` preserves the cokernel `F^p A / F^{p + 1} A` defining `gr^p`. -/
public noncomputable def gradedPieceSingleFilIso (j p : ℤ) (A : FilteredObject 𝒜 ℤᵒᵖ) :
    (gr p).obj ((singleFil j).obj A) ≅
      (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).obj ((gr p).obj A) :=
  (PreservesCokernel.iso (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j)
    (A.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)).symm

/-- `gradedPieceSingleFilIso` is natural in `A`, read on the inverse: this is the form the
comparison of short complexes below consumes. -/
public lemma gradedPieceSingleFilIso_inv_naturality (j p : ℤ) {A B : FilteredObject 𝒜 ℤᵒᵖ}
    (f : A ⟶ B) :
    (gradedPieceSingleFilIso j p A).inv ≫
        (gr p).map ((singleFil j).map f) =
      (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map ((gr p).map f) ≫
        (gradedPieceSingleFilIso j p B).inv :=
  preserves_cokernel_iso_comp_cokernel_map
    (G := HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j)
    (f := A.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
    (g := B.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
    (p := f.natTrans.app (op (p + 1))) (q := f.natTrans.app (op p))
    (hpq := f.natTrans.naturality _)

/-- `gradedPieceSingleFilIso` is natural in `A`: the square of a morphism `f : A ⟶ B` commutes. -/
public lemma gradedPieceSingleFilIso_naturality (j p : ℤ) {A B : FilteredObject 𝒜 ℤᵒᵖ}
    (f : A ⟶ B) :
    (gr p).map ((singleFil j).map f) ≫
        (gradedPieceSingleFilIso j p B).hom =
      (gradedPieceSingleFilIso j p A).hom ≫
        (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map ((gr p).map f) := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, gradedPieceSingleFilIso_inv_naturality,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

open CochainComplex.FilteredInjective.Resolution in
/-- **Short exactness of the graded pieces is preserved by placing in a degree.** For a sequence
`0 → A → B → C → 0` of filtered objects with vanishing composite whose graded pieces are short
exact, the graded pieces of `0 → A[j] → B[j] → C[j] → 0` are short exact: they are the graded
pieces of the first sequence placed in degree `j`, and `HomologicalComplex.single` is exact. This
is the hypothesis `hgr` of [Stacks, Tag 05TV]. -/
public lemma shortExact_gradedPiece_singleFil_map {A B C : FilteredObject 𝒜 ℤᵒᵖ} (j : ℤ)
    (α : A ⟶ B) (β : B ⟶ C) (hαβ : (α ≫ β).hom = 0)
    (hgr : ∀ (p : ℤ) (h : (gr p).map α ≫ (gr p).map β = 0),
      (ShortComplex.mk _ _ h).ShortExact)
    (p : ℤ) (h : (gr p).map ((singleFil j).map α) ≫
      (gr p).map ((singleFil j).map β) = 0) :
    (ShortComplex.mk _ _ h).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (gradedPieceSingleFilIso j p A).symm (gradedPieceSingleFilIso j p B).symm
      (gradedPieceSingleFilIso j p C).symm (gradedPieceSingleFilIso_inv_naturality j p α)
      (gradedPieceSingleFilIso_inv_naturality j p β))
    ((hgr p (gradedPiece_map_comp_eq_zero α β hαβ p)).map_of_exact
      (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j))

/-- **A finite filtration placed in a degree is degreewise finite.** In degrees other than `j` both
the complex and its filtration steps vanish, and in degree `j` the filtration is that of `A`. This
is the degreewise finiteness [Stacks, Tag 05TT] and [Stacks, Tag 05TV] take. -/
public lemma isDegreewiseFinite_singleFil (j : ℤ) {A : FilteredObject 𝒜 ℤᵒᵖ}
    (hA : A.filtration.IsFinite) (n : ℤ) :
    ∃ p q : ℤ, IsIso ((((singleFil j).obj A).filtration.ι.app (op p)).f n) ∧
      IsZero ((((singleFil j).obj A).filtration.obj (op q)).X n) := by
  obtain ⟨p, hp⟩ := hA.exists_isIso_ι
  obtain ⟨q, hq⟩ := hA.exists_isZero_obj
  refine ⟨p, q, ?_, ?_⟩
  · have := hp
    exact inferInstanceAs (IsIso ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n).map
      ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j).map (A.filtration.ι.app (op p)))))
  · exact Functor.map_isZero (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
      (Functor.map_isZero (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) j) hq)

end CategoryTheory.FilteredObject

end SingleDegree

section TermwiseSplitConsequences

namespace CochainComplex

open CategoryTheory.FilteredObject CochainComplex.FilteredInjective.Resolution

/-- A morphism of filtered complexes, read in a fixed degree. -/
@[implicit_reducible]
private noncomputable def evalHom {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (γ : K ⟶ L)
    (n : ℤ) : evalFil K n ⟶ evalFil L n :=
  FilteredObject.homMk (γ.hom.f n) (fun i => (γ.natTrans.app i).f n)
    (fun i => congrArg (fun g : K.filtration.obj i ⟶ L.X => g.f n) (γ.comm i))

@[local simp]
private lemma evalHom_hom {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (γ : K ⟶ L) (n : ℤ) :
    (evalHom γ n).hom = γ.hom.f n :=
  rfl

@[local simp]
private lemma evalHom_natTrans_app {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (γ : K ⟶ L)
    (n : ℤ) (i : ℤᵒᵖ) : (evalHom γ n).natTrans.app i = (γ.natTrans.app i).f n :=
  rfl

/-- The identification of `gr^p` in degree `n` with `gr^p` of the degree `n` filtered object is
natural. -/
private lemma evalGradedPieceIso_hom_naturality {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (γ : K ⟶ L) (p n : ℤ) :
    (evalGradedPieceIso K p n).hom ≫ (gr p).map (evalHom γ n) =
      ((gr p).map γ).f n ≫ (evalGradedPieceIso L p n).hom :=
  preserves_cokernel_iso_comp_cokernel_map
    (G := HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
    (f := K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
    (g := L.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
    (p := γ.natTrans.app (op (p + 1))) (q := γ.natTrans.app (op p))
    (hpq := γ.natTrans.naturality _)

private lemma evalGradedPieceIso_inv_naturality {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (γ : K ⟶ L) (p n : ℤ) :
    (evalGradedPieceIso K p n).inv ≫ ((gr p).map γ).f n =
      (gr p).map (evalHom γ n) ≫ (evalGradedPieceIso L p n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, evalGradedPieceIso_hom_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- A filtration step of a morphism of filtered complexes sits over the morphism, in each
degree. -/
private lemma natTrans_app_f_comp_ι_app_f {K L : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (γ : K ⟶ L) (i : ℤᵒᵖ) (n : ℤ) :
    (γ.natTrans.app i).f n ≫ (L.filtration.ι.app i).f n =
      (K.filtration.ι.app i).f n ≫ γ.hom.f n := by
  have h := γ.comm i
  dsimp only [Functor.const_obj_obj] at h
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, h]

private lemma hom_f_comp_hom_f {I M J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (u : I ⟶ M)
    (v : M ⟶ J) (huv : u.hom ≫ v.hom = 0) (n : ℤ) : u.hom.f n ≫ v.hom.f n = 0 := by
  rw [← HomologicalComplex.comp_f, huv, HomologicalComplex.zero_f]

private lemma natTrans_app_f_comp_natTrans_app_f
    {I M J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (u : I ⟶ M) (v : M ⟶ J)
    (huv : u.hom ≫ v.hom = 0) (i : ℤᵒᵖ) (n : ℤ) :
    (u.natTrans.app i).f n ≫ (v.natTrans.app i).f n = 0 := by
  rw [← HomologicalComplex.comp_f, show u.natTrans.app i ≫ v.natTrans.app i = 0 from
    natTrans_app_eq_zero (u ≫ v) (by simpa using huv) i, HomologicalComplex.zero_f]

private lemma evalHom_comp_hom_eq_zero {I M J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (u : I ⟶ M) (v : M ⟶ J) (huv : u.hom ≫ v.hom = 0) (n : ℤ) :
    (evalHom u n ≫ evalHom v n).hom = 0 :=
  hom_f_comp_hom_f u v huv n

/-- The middle term of a split short complex vanishes when the outer terms do. -/
private lemma isZero_of_splitting {S : ShortComplex 𝒜} (σ : S.Splitting) (h₁ : IsZero S.X₁)
    (h₃ : IsZero S.X₃) : IsZero S.X₂ :=
  IsZero.of_iso (isZero_biprod h₁ h₃) σ.isoBinaryBiproduct

/-- **Correcting a retraction by a section.** In a short exact sequence, a retraction `r` of `f`
and a section `s` of `g` become complementary once `r` is replaced by `r - g ≫ s ≫ r`: the
retraction complementary to `s` is unique, and it is a retraction because the sequence is exact. -/
private lemma comp_add_comp_eq_id_of_section {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂) (hr : S.f ≫ r = 𝟙 S.X₁) (hs : s ≫ S.g = 𝟙 S.X₃) :
    S.f ≫ (r - S.g ≫ s ≫ r) = 𝟙 S.X₁ ∧
      (r - S.g ≫ s ≫ r) ≫ S.f + S.g ≫ s = 𝟙 S.X₂ := by
  have hmono := hS.mono_f
  obtain ⟨r', hr', hid'⟩ :
      ∃ r' : S.X₂ ⟶ S.X₁, S.f ≫ r' = 𝟙 S.X₁ ∧ r' ≫ S.f + S.g ≫ s = 𝟙 S.X₂ :=
    ⟨(ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hmono).r,
      (ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hmono).f_r,
      (ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hmono).id⟩
  have hrr : r' = r - S.g ≫ s ≫ r := by
    conv_lhs => rw [← Category.comp_id r', ← hr, ← Category.assoc,
      show r' ≫ S.f = 𝟙 S.X₂ - S.g ≫ s from eq_sub_of_add_eq hid']
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc]
  rw [← hrr]
  exact ⟨hr', hid'⟩

/-- **The termwise splitting of [Stacks, Tag 05TV], normalised.** The retraction corrected by the
section is complementary to it, both on the underlying objects and on every filtration step; on the
steps the identities are those of the underlying objects, read through the monomorphisms
`F^p M^n ⟶ M^n`. -/
private lemma exists_complementary_termwiseSplitting
    {I M J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (u : I ⟶ M) (v : M ⟶ J)
    (huv : u.hom ≫ v.hom = 0) (hSE : (ShortComplex.mk u.hom v.hom huv).ShortExact)
    (hsplit : ∀ n : ℤ, ∃ (r : M.X.X n ⟶ I.X.X n) (s : J.X.X n ⟶ M.X.X n),
      u.hom.f n ≫ r = 𝟙 (I.X.X n) ∧ s ≫ v.hom.f n = 𝟙 (J.X.X n) ∧
      (∀ p : ℤ, ∃ rp : (M.filtration.obj (op p)).X n ⟶ (I.filtration.obj (op p)).X n,
        rp ≫ (I.filtration.ι.app (op p)).f n = (M.filtration.ι.app (op p)).f n ≫ r) ∧
      (∀ p : ℤ, ∃ sp : (J.filtration.obj (op p)).X n ⟶ (M.filtration.obj (op p)).X n,
        sp ≫ (M.filtration.ι.app (op p)).f n = (J.filtration.ι.app (op p)).f n ≫ s))
    (n : ℤ) :
    ∃ (r : M.X.X n ⟶ I.X.X n) (s : J.X.X n ⟶ M.X.X n)
      (rp : ∀ p : ℤ, (M.filtration.obj (op p)).X n ⟶ (I.filtration.obj (op p)).X n)
      (sp : ∀ p : ℤ, (J.filtration.obj (op p)).X n ⟶ (M.filtration.obj (op p)).X n),
      u.hom.f n ≫ r = 𝟙 (I.X.X n) ∧ s ≫ v.hom.f n = 𝟙 (J.X.X n) ∧
      r ≫ u.hom.f n + v.hom.f n ≫ s = 𝟙 (M.X.X n) ∧
      (∀ p : ℤ, (u.natTrans.app (op p)).f n ≫ rp p = 𝟙 ((I.filtration.obj (op p)).X n)) ∧
      (∀ p : ℤ, sp p ≫ (v.natTrans.app (op p)).f n = 𝟙 ((J.filtration.obj (op p)).X n)) ∧
      (∀ p : ℤ, rp p ≫ (u.natTrans.app (op p)).f n + (v.natTrans.app (op p)).f n ≫ sp p =
        𝟙 ((M.filtration.obj (op p)).X n)) ∧
      (∀ p : ℤ, rp p ≫ (I.filtration.ι.app (op p)).f n =
        (M.filtration.ι.app (op p)).f n ≫ r) ∧
      (∀ p : ℤ, sp p ≫ (M.filtration.ι.app (op p)).f n =
        (J.filtration.ι.app (op p)).f n ≫ s) := by
  obtain ⟨r₀, s, hur₀, hsv, hr₀, hs⟩ := hsplit n
  choose rp₀ hrp₀ using hr₀
  choose sp hsp using hs
  have hSEn : (ShortComplex.mk (u.hom.f n) (v.hom.f n) (hom_f_comp_hom_f u v huv n)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hSE n
  obtain ⟨hur, hid⟩ := comp_add_comp_eq_id_of_section hSEn r₀ s hur₀ hsv
  have hv : ∀ p : ℤ, (v.natTrans.app (op p)).f n ≫ (J.filtration.ι.app (op p)).f n =
      (M.filtration.ι.app (op p)).f n ≫ v.hom.f n := fun p =>
    natTrans_app_f_comp_ι_app_f v (op p) n
  have hup : ∀ p : ℤ, (u.natTrans.app (op p)).f n ≫ rp₀ p = 𝟙 _ := fun p => by
    have := mono_ι_app_f I (op p) n
    rw [← cancel_mono ((I.filtration.ι.app (op p)).f n)]
    simp [hrp₀ p, reassoc_of% (natTrans_app_f_comp_ι_app_f u (op p) n), hur₀]
  have hsvp : ∀ p : ℤ, sp p ≫ (v.natTrans.app (op p)).f n = 𝟙 _ := fun p => by
    have := mono_ι_app_f J (op p) n
    rw [← cancel_mono ((J.filtration.ι.app (op p)).f n)]
    simp [hv p, reassoc_of% (hsp p), hsv]
  have h4 : ∀ p : ℤ, (rp₀ p - (v.natTrans.app (op p)).f n ≫ sp p ≫ rp₀ p) ≫
      (I.filtration.ι.app (op p)).f n =
      (M.filtration.ι.app (op p)).f n ≫ (r₀ - v.hom.f n ≫ s ≫ r₀) := fun p => by
    simp [hrp₀ p, reassoc_of% (hsp p), reassoc_of% (hv p)]
  refine ⟨r₀ - v.hom.f n ≫ s ≫ r₀, s,
    fun p => rp₀ p - (v.natTrans.app (op p)).f n ≫ sp p ≫ rp₀ p, sp, hur, hsv, hid,
    fun p => ?_, hsvp, fun p => ?_, h4, hsp⟩
  · simp [reassoc_of% (natTrans_app_f_comp_natTrans_app_f u v huv (op p) n), hup p]
  · have := mono_ι_app_f M (op p) n
    rw [← cancel_mono ((M.filtration.ι.app (op p)).f n)]
    simp only [Preadditive.add_comp, Category.assoc, natTrans_app_f_comp_ι_app_f u (op p) n,
      hsp p, reassoc_of% (h4 p), reassoc_of% (hv p), ← Preadditive.comp_add]
    simpa using (M.filtration.ι.app (op p)).f n ≫= hid

/-- **The graded pieces of the termwise split sequence are split.** The complementary retraction
and section of a degree are morphisms of filtered objects, the structure maps `F^p M^n ⟶ M^n` being
monomorphisms, and `gr^p` carries their identities to a splitting of
`0 → gr^p I^n → gr^p M^n → gr^p J^n → 0`. -/
private lemma nonempty_gradedPiece_splitting
    {I M J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (u : I ⟶ M) (v : M ⟶ J)
    (huv : u.hom ≫ v.hom = 0) (hSE : (ShortComplex.mk u.hom v.hom huv).ShortExact)
    (hsplit : ∀ n : ℤ, ∃ (r : M.X.X n ⟶ I.X.X n) (s : J.X.X n ⟶ M.X.X n),
      u.hom.f n ≫ r = 𝟙 (I.X.X n) ∧ s ≫ v.hom.f n = 𝟙 (J.X.X n) ∧
      (∀ p : ℤ, ∃ rp : (M.filtration.obj (op p)).X n ⟶ (I.filtration.obj (op p)).X n,
        rp ≫ (I.filtration.ι.app (op p)).f n = (M.filtration.ι.app (op p)).f n ≫ r) ∧
      (∀ p : ℤ, ∃ sp : (J.filtration.obj (op p)).X n ⟶ (M.filtration.obj (op p)).X n,
        sp ≫ (M.filtration.ι.app (op p)).f n = (J.filtration.ι.app (op p)).f n ≫ s))
    (p n : ℤ) :
    Nonempty (ShortComplex.mk ((gr p).map (evalHom u n))
      ((gr p).map (evalHom v n))
      (gradedPiece_map_comp_eq_zero (evalHom u n) (evalHom v n)
        (evalHom_comp_hom_eq_zero u v huv n) p)).Splitting := by
  obtain ⟨r, s, rp, sp, hur, hsv, hid, h1, h2, h3, h4, h5⟩ :=
    exists_complementary_termwiseSplitting u v huv hSE hsplit n
  obtain ⟨R, S, hRu, hSv, hRS⟩ : ∃ (R : evalFil M n ⟶ evalFil I n) (S : evalFil J n ⟶ evalFil M n),
      evalHom u n ≫ R = 𝟙 (evalFil I n) ∧ S ≫ evalHom v n = 𝟙 (evalFil J n) ∧
      ∀ q : ℤ, R.natTrans.app (op q) ≫ (evalHom u n).natTrans.app (op q) +
        (evalHom v n).natTrans.app (op q) ≫ S.natTrans.app (op q) =
        𝟙 ((evalFil M n).filtration.obj (op q)) :=
    ⟨FilteredObject.homMk r (fun i => rp i.unop) (fun i => h4 i.unop),
      FilteredObject.homMk s (fun i => sp i.unop) (fun i => h5 i.unop),
      FilteredObject.hom_ext hur, FilteredObject.hom_ext hsv, h3⟩
  have ha : (gr p).map (evalHom u n) ≫ (gr p).map R = 𝟙 _ := by
    rw [← Functor.map_comp, hRu, CategoryTheory.Functor.map_id]
  have hb : (gr p).map S ≫ (gr p).map (evalHom v n) = 𝟙 _ := by
    rw [← Functor.map_comp, hSv, CategoryTheory.Functor.map_id]
  have hc : (gr p).map R ≫ (gr p).map (evalHom u n) +
      (gr p).map (evalHom v n) ≫ (gr p).map S = 𝟙 _ := by
    rw [← cancel_epi (grMapπ (succHom p) (evalFil M n)), Preadditive.comp_add, Category.comp_id,
      ← Category.assoc, ← Category.assoc, grMapπ_map, grMapπ_map,
      Category.assoc, Category.assoc, grMapπ_map, grMapπ_map,
      ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp]
    exact (congrArg (fun x => x ≫ grMapπ (succHom p) (evalFil M n)) (hRS p)).trans
      (Category.id_comp _)
  exact ⟨⟨(gr p).map R, (gr p).map S, ha, hb, hc⟩⟩

/-- **What the termwise splitting of [Stacks, Tag 05TV] gives.** In the situation of that lemma —
a short exact sequence `0 → A → B → C → 0` of `Fil^f(𝒜)` placed in degree `0`, filtered
quasi-isomorphisms `a : A[0] ⟶ I^•` and `c : C[0] ⟶ J^•` into complexes of filtered objects with
degreewise finite filtrations vanishing in negative degrees and with filtered injective terms, and
the complex `M^•` with `u`, `v`, `b` that it produces — the complex `M^•` vanishes in negative
degrees, each `M^n` has finite filtration, each `gr^p(M^n)` is an injective object of `𝒜`, and
`b : B[0] ⟶ M^•` is a filtered quasi-isomorphism. Filtered injectivity of `J^•` is an extra
hypothesis, satisfied where [Stacks, Tag 05TW] applies this, `J^•` being a filtered injective
resolution as well. -/
public theorem isStrictlyGE_isDegreewiseFinite_injective_gr_filteredQuasiIso_of_termwiseSplit
    {A B C I J M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [I.X.IsStrictlyGE 0] [J.X.IsStrictlyGE 0]
    (α : A ⟶ B) (β : B ⟶ C) (a : A ⟶ I) (c : C ⟶ J) (u : I ⟶ M) (v : M ⟶ J) (b : B ⟶ M)
    (hcomp : α.hom ≫ β.hom = 0)
    (hgr : ∀ (p : ℤ) (h : (gr p).map α ≫
        (gr p).map β = 0),
      (ShortComplex.mk _ _ h).ShortExact)
    (ha : filteredQuasiIso 𝒜 a) (hc : filteredQuasiIso 𝒜 c)
    (hIfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((I.filtration.ι.app (op p)).f n) ∧
      IsZero ((I.filtration.obj (op q)).X n))
    (hJfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((J.filtration.ι.app (op p)).f n) ∧
      IsZero ((J.filtration.obj (op q)).X n))
    (hIinj : ∀ p n : ℤ, Injective (((gr p).obj I).X n))
    (hJinj : ∀ p n : ℤ, Injective (((gr p).obj J).X n))
    (huv : u.hom ≫ v.hom = 0) (hSE : (ShortComplex.mk u.hom v.hom huv).ShortExact)
    (hαb : α ≫ b = a ≫ u) (hbv : b ≫ v = β ≫ c)
    (hsplit : ∀ n : ℤ, ∃ (r : M.X.X n ⟶ I.X.X n) (s : J.X.X n ⟶ M.X.X n),
      u.hom.f n ≫ r = 𝟙 (I.X.X n) ∧ s ≫ v.hom.f n = 𝟙 (J.X.X n) ∧
      (∀ p : ℤ, ∃ rp : (M.filtration.obj (op p)).X n ⟶ (I.filtration.obj (op p)).X n,
        rp ≫ (I.filtration.ι.app (op p)).f n = (M.filtration.ι.app (op p)).f n ≫ r) ∧
      (∀ p : ℤ, ∃ sp : (J.filtration.obj (op p)).X n ⟶ (M.filtration.obj (op p)).X n,
        sp ≫ (M.filtration.ι.app (op p)).f n = (J.filtration.ι.app (op p)).f n ≫ s)) :
    M.X.IsStrictlyGE 0 ∧
      (∀ n : ℤ, ∃ p q : ℤ, IsIso ((M.filtration.ι.app (op p)).f n) ∧
        IsZero ((M.filtration.obj (op q)).X n)) ∧
      (∀ p n : ℤ, Injective (((gr p).obj M).X n)) ∧
      filteredQuasiIso 𝒜 b :=
  ⟨by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    obtain ⟨r, s, rp, sp, hur, hsv, hid, -, -, -, -, -⟩ :=
      exists_complementary_termwiseSplitting u v huv hSE hsplit n
    exact isZero_of_splitting
      (S := ShortComplex.mk (u.hom.f n) (v.hom.f n) (hom_f_comp_hom_f u v huv n))
      ⟨r, s, hur, hsv, hid⟩ (I.X.isZero_of_isStrictlyGE 0 n hn) (J.X.isZero_of_isStrictlyGE 0 n hn),
  by
    intro n
    obtain ⟨r, s, rp, sp, hur, hsv, hid, h1, h2, h3, h4, h5⟩ :=
      exists_complementary_termwiseSplitting u v huv hSE hsplit n
    obtain ⟨pI, qI, hpI, hqI⟩ := hIfin n
    obtain ⟨pJ, qJ, hpJ, hqJ⟩ := hJfin n
    let σp (p : ℤ) : (ShortComplex.mk ((u.natTrans.app (op p)).f n) ((v.natTrans.app (op p)).f n)
        (natTrans_app_f_comp_natTrans_app_f u v huv (op p) n)).Splitting :=
      ⟨rp p, sp p, h1 _, h2 _, h3 _⟩
    have key : ∀ m : ℤ, IsIso ((I.filtration.ι.app (op m)).f n) →
        IsIso ((J.filtration.ι.app (op m)).f n) → IsIso ((M.filtration.ι.app (op m)).f n) := by
      intro m _ _
      have hsq : biprod.desc ((u.natTrans.app (op m)).f n) (sp m) ≫
            (M.filtration.ι.app (op m)).f n =
          biprod.map ((I.filtration.ι.app (op m)).f n) ((J.filtration.ι.app (op m)).f n) ≫
            biprod.desc (u.hom.f n) s := by
        refine biprod.hom_ext' _ _ ?_ ?_
        · rw [biprod.inl_desc_assoc, ← Category.assoc, biprod.inl_map, Category.assoc,
            biprod.inl_desc, natTrans_app_f_comp_ι_app_f]
        · rw [biprod.inr_desc_assoc, ← Category.assoc, biprod.inr_map, Category.assoc,
            biprod.inr_desc, h5]
      have hisoσ : IsIso (biprod.desc (u.hom.f n) s) :=
        (ShortComplex.Splitting.isoBinaryBiproduct
          (S := ShortComplex.mk (u.hom.f n) (v.hom.f n) (hom_f_comp_hom_f u v huv n))
          ⟨r, s, hur, hsv, hid⟩).isIso_inv
      have : IsIso (biprod.desc ((u.natTrans.app (op m)).f n) (sp m)) :=
        (σp m).isoBinaryBiproduct.isIso_inv
      have : IsIso (biprod.desc ((u.natTrans.app (op m)).f n) (sp m) ≫
          (M.filtration.ι.app (op m)).f n) := by
        rw [hsq]
        exact IsIso.comp_isIso' (isIso_biprod_map _ _) hisoσ
      exact IsIso.of_isIso_comp_left (biprod.desc ((u.natTrans.app (op m)).f n) (sp m)) _
    exact ⟨min pI pJ, max qI qJ,
      key _ (isIso_ι_f_of_le I (min_le_left pI pJ) hpI)
        (isIso_ι_f_of_le J (min_le_right pI pJ) hpJ),
      isZero_of_splitting (σp _) (isZero_fil_X_of_le I (le_max_left qI qJ) hqI)
        (isZero_fil_X_of_le J (le_max_right qI qJ) hqJ)⟩,
  by
    intro p n
    obtain ⟨σ⟩ := nonempty_gradedPiece_splitting u v huv hSE hsplit p n
    have hI' : Injective ((gr p).obj (evalFil I n)) :=
      Injective.of_iso (evalGradedPieceIso I p n) (hIinj p n)
    have hJ' : Injective ((gr p).obj (evalFil J n)) :=
      Injective.of_iso (evalGradedPieceIso J p n) (hJinj p n)
    have hM : Injective ((gr p).obj (evalFil M n)) :=
      Injective.of_iso σ.isoBinaryBiproduct.symm
        (inferInstanceAs (Injective ((gr p).obj (evalFil I n) ⊞
          (gr p).obj (evalFil J n))))
    exact Injective.of_iso (evalGradedPieceIso M p n).symm hM,
  fun p => by
    have hzuv : (gr p).map u ≫
        (gr p).map v = 0 :=
      gradedPiece_map_comp_eq_zero u v (by simpa using huv) p
    have hrow2 : (ShortComplex.mk ((gr p).map u)
        ((gr p).map v) hzuv).ShortExact := by
      refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
      obtain ⟨σ⟩ := nonempty_gradedPiece_splitting u v huv hSE hsplit p n
      exact ShortComplex.shortExact_of_iso
        (ShortComplex.isoMk (evalGradedPieceIso I p n).symm (evalGradedPieceIso M p n).symm
          (evalGradedPieceIso J p n).symm
          (evalGradedPieceIso_inv_naturality u p n) (evalGradedPieceIso_inv_naturality v p n))
        σ.shortExact
    have hτ₁ : QuasiIso ((gr p).map a) := ha p
    have hτ₃ : QuasiIso ((gr p).map c) := hc p
    exact StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂
      (S₁ := ShortComplex.mk _ _ (gradedPiece_map_comp_eq_zero α β (by simpa using hcomp) p))
      (S₂ := ShortComplex.mk _ _ hzuv)
      ⟨(gr p).map a, (gr p).map b,
        (gr p).map c,
        by rw [← Functor.map_comp, ← Functor.map_comp, hαb],
        by rw [← Functor.map_comp, ← Functor.map_comp, hbv]⟩
      (hgr p _) hrow2⟩

end CochainComplex

end TermwiseSplitConsequences

end
