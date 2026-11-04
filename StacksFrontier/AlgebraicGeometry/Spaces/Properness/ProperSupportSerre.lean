module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# Extensions, images, cokernels and the Serre subcategory of modules with proper support

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type.  **Stacks 0CZK** collects the closure properties of the condition "the support is proper
over `Y`" of Stacks 0CZD: part (1) says that the condition passes to a direct sum, to an
extension, to the image and the cokernel of a map, and to a quotient; part (2) says that the
coherent `𝒪_X`-modules satisfying it form a Serre subcategory of `Coh(𝒪_X)`.

The direct sum clause is
`AlgebraicGeometry.Space.hasProperSupport_toSheaf_of_sectionwiseSplit` and the quotient clause
is `AlgebraicGeometry.Space.hasProperSupport_of_epi`.  This file supplies the three remaining
clauses of part (1) and the whole of part (2).

## Main results

* `AlgebraicGeometry.Space.isProperOver_empty`: the empty subset of the point set is proper
  over the base.
* `AlgebraicGeometry.Space.hasProperSupport_X₂_of_shortExact`: **Stacks 0CZK**, the extension
  clause of part (1).
* `AlgebraicGeometry.Space.hasProperSupport_cokernel`: **Stacks 0CZK**, the cokernel clause of
  part (1).
* `AlgebraicGeometry.Space.hasProperSupport_abelianImage`: **Stacks 0CZK**, the image clause of
  part (1).
* `AlgebraicGeometry.Space.isSerreClass_isCoherentProperOver`: **Stacks 0CZK**, part (2).

## Implementation notes

**The extension clause needs no finiteness at all.**  `HasProperSupport` carries closedness of
the support as an existential witness, and closedness is the one thing a containment of
supports does not give; that is why the clauses of part (1) were held up on the finite type
closure of Properties of Spaces, Section 66.30 (Stacks 05VR).  For an extension the obstruction
disappears, exactly as it does for a direct sum: the support of the middle term of a short exact
sequence is *contained* in the union of the supports of the outer terms
(`AlgebraicGeometry.Space.supportOfSheaf_middle_subset_union`) and *contains* each of them, the
first inclusion of the outer terms being a monomorphism and the second projection a local
surjection (both halves of Stacks 04KB).  So the support of the extension is the union of two
supports already known to be closed, and Stacks 0CZH finishes.

**The cokernel and the image are quotients.**  The cokernel of `u : F ⟶ G` is a quotient of `G`
and the image of `u` is a quotient of `F` — the latter through
`CategoryTheory.Abelian.coimage`, which is literally `cokernel (kernel.ι u)`, and the canonical
isomorphism `CategoryTheory.Abelian.coimageIsoImage`.  Both clauses are therefore the quotient
clause `AlgebraicGeometry.Space.hasProperSupport_of_epi`, which asks finite type of the module
being divided and nothing of the other one.  Accordingly the cokernel clause hypothesizes
proper support of `G` only and the image clause proper support of `F` only, where Stacks 0CZK
assumes it of both; each is the source's statement with the unused half of its hypothesis
dropped.

**Part (2) is stated without the locally Noetherian hypothesis on `Y`.**  In the source that
hypothesis is what makes `Coh(𝒪_X)` abelian — Stacks 07UC, reached through the identification
of coherence with quasi-coherence plus finite type over a locally Noetherian space.  In this
tree `AlgebraicGeometry.Space.IsCoherent` carries the sectionwise coherence condition of
Stacks 03DL(8) directly, so the abelian structure is available with no hypothesis at all:
see the module documentation of `StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian`, which
lands Stacks 07UC in that generality.  Carrying the hypothesis here would therefore be dead
weight, and the statement below specializes to Stacks 0CZK part (2) when `Y` is locally
Noetherian.

The abelian structure is introduced by a `let` in the statement, since
`CategoryTheory.ObjectProperty.IsSerreClass` is stated for an abelian ambient category and
`AlgebraicGeometry.Space.coherentModules_abelian_of_closure` is deliberately not an instance.
The Serre class itself is the object property
`AlgebraicGeometry.Space.isCoherentProperOver` already used to cut out the source of equation
76.42.5.1 in `StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicSystemProperSupport`; no new
predicate is introduced.

Part (2) is proved through Stacks 02MP,
`CategoryTheory.ObjectProperty.isSerreClass_iff_prop_X₂_of_exact`, which reduces a Serre class
to one exactness condition together with nonemptiness.  The nonempty witness is the zero
module, whose support is empty; the exactness condition is run in the ambient category of all
`𝒪_X`-modules, where the kernel of `T.X₂ ⟶ T.X₃` is a quotient of `T.X₁` by exactness, has
proper support by the quotient clause, and bounds the support of `T.X₂` together with the support
of `T.X₃` by
`AlgebraicGeometry.Space.supportOfSheaf_subset_union_kernel`.  Closedness of the support of
`T.X₂` is free there because a coherent module is of finite type.

## References

* [Stacks Project, Tag 0CZK](https://stacks.math.columbia.edu/tag/0CZK)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZE](https://stacks.math.columbia.edu/tag/0CZE)
* [Stacks Project, Tag 0CZH](https://stacks.math.columbia.edu/tag/0CZH)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 02MP](https://stacks.math.columbia.edu/tag/02MP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The empty support -/

/-- **The empty subset of the point set of `X` is proper over `Y`.**  It is the union of the
empty family of closed subsets proper over `Y`, so Stacks 0CZH applies to it; the comparison
with that union is Stacks 0CZE. -/
theorem isProperOver_empty (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    IsProperOver B S hS hX hY f hf (∅ : Set (points B S hS X)) isClosed_empty := by
  refine isProperOver_of_subset B S hS hX hY f hf ∅
    (⋃ _ : Fin 0, (∅ : Set (points B S hS X))) isClosed_empty
    (isClosed_iUnion_of_finite fun _ => isClosed_empty) (Set.empty_subset _) ?_
  exact isProperOver_iUnion B S hS hX hY f hf (fun _ : Fin 0 => ∅)
    (fun _ => isClosed_empty) (fun i => i.elim0)

/-- **A zero `𝒪_X`-module has support proper over `Y`.**  Its support is empty, by
`AlgebraicGeometry.Space.supportOfSheaf_eq_empty_iff_isZero`, and the empty set is proper over
`Y`. -/
theorem hasProperSupport_of_isZero (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {M : Modules.{u, u} B S hS X hX} (hM : IsZero M) :
    HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj M) := by
  have hsupp : supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj M) = ∅ :=
    (supportOfSheaf_eq_empty_iff_isZero B S hS ⟨X, hX⟩ M).2 hM
  have hcl : IsClosed (supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj M)) := by
    rw [hsupp]; exact isClosed_empty
  exact ⟨hcl, isProperOver_of_subset B S hS hX hY f hf _ ∅ hcl isClosed_empty hsupp.subset
    (isProperOver_empty B S hS hX hY f hf)⟩

/-! ### Stacks 0CZK, part (1): extensions, cokernels and images -/

/-- **Stacks 0CZK, part (1), the extension clause.**  An extension of `𝒪_X`-modules whose
supports are proper over `Y` again has support proper over `Y`: the middle term of a short exact
sequence of `𝒪_X`-modules whose outer terms have support proper over `Y` has support proper
over `Y`.

The support of the middle term is *exactly* the union of the supports of the outer two.  It is
contained in that union by
`AlgebraicGeometry.Space.supportOfSheaf_middle_subset_union`; it contains the support of the
first term because the first map is a monomorphism and the support of the third because the
second map is an epimorphism, hence a local surjection, which are the two halves of Stacks
04KB.  So the support is closed, being a union of two closed supports, and a finite union of
closed subsets proper over `Y` is proper over `Y` by Stacks 0CZH.

No finiteness hypothesis appears: as for a direct sum, the containment of supports is an
equality, so closedness of the support of the extension comes from the two given supports and
not from the finite type closure of Stacks 05VR. -/
@[stacks 0CZK "part (1), extensions"]
theorem hasProperSupport_X₂_of_shortExact (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {T : ShortComplex (Modules.{u, u} B S hS X hX)} (hT : T.ShortExact)
    (h₁ : HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj T.X₁))
    (h₃ : HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj T.X₃)) :
    HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj T.X₂) := by
  obtain ⟨hcl₁, hp₁⟩ := h₁
  obtain ⟨hcl₃, hp₃⟩ := h₃
  have _ : Mono T.f := hT.mono_f
  have _ : Epi T.g := hT.epi_g
  have hmono : Mono ((SheafOfModules.toSheaf _).map T.f) :=
    preserves_mono_of_preservesLimit _ T.f
  have hsub := supportOfSheaf_middle_subset_union B S hS ⟨X, hX⟩ T hT
  have hsub₁ : supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj T.X₁) ⊆
      supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj T.X₂) :=
    @supportOfSheaf_subset_of_mono B S hS X hX _ _
      ((SheafOfModules.toSheaf _).map T.f) hmono
  have hsub₃ : supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj T.X₃) ⊆
      supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj T.X₂) :=
    @supportOfSheaf_subset_of_isLocallySurjective B S hS X hX _ _
      ((SheafOfModules.toSheaf _).map T.g)
      (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi T.g)
  have heq : supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj T.X₂) =
      supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj T.X₁) ∪
        supportOfSheaf B S hS X ((SheafOfModules.toSheaf _).obj T.X₃) :=
    subset_antisymm hsub (Set.union_subset hsub₁ hsub₃)
  refine hasProperSupport_of_subset_union B S hS hX hY f hf ?_ hsub ⟨hcl₁, hp₁⟩ ⟨hcl₃, hp₃⟩
  rw [heq]
  exact hcl₁.union hcl₃

/-- **Stacks 0CZK, part (1), the cokernel clause.**  The cokernel of a map `u : M ⟶ N` of
`𝒪_X`-modules whose target is of finite type and has support proper over `Y` again has support
proper over `Y`.

The cokernel is a quotient of `N`, so this is the quotient clause
`AlgebraicGeometry.Space.hasProperSupport_of_epi`.  Stacks 0CZK assumes proper support of both
`M` and `N`; the source of `u` plays no part. -/
@[stacks 0CZK "part (1), cokernels"]
theorem hasProperSupport_cokernel (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {M N : Modules.{u, u} B S hS X hX} (u : M ⟶ N)
    (hNft : SheafOfModules.IsFiniteTypeOnSite N)
    (hN : HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj N)) :
    HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj
      (cokernel (C := Modules.{u, u} B S hS X hX) u)) :=
  hasProperSupport_of_epi B S hS hX hY f hf
    (cokernel.π (C := Modules.{u, u} B S hS X hX) u) hNft hN

/-- **Stacks 0CZK, part (1), the image clause.**  The image of a map `u : M ⟶ N` of
`𝒪_X`-modules whose source is of finite type and has support proper over `Y` again has support
proper over `Y`.

`CategoryTheory.Abelian.coimage u` is by definition `cokernel (kernel.ι u)`, hence a quotient of
`M`, so it has support proper over `Y` by the quotient clause
`AlgebraicGeometry.Space.hasProperSupport_of_epi`; and
`CategoryTheory.Abelian.coimageIsoImage` identifies it with the image, whose support is
therefore the same by Stacks 04KB.  Stacks 0CZK assumes proper support of both `M` and `N`; the
target of `u` plays no part. -/
@[stacks 0CZK "part (1), images"]
theorem hasProperSupport_abelianImage (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    {M N : Modules.{u, u} B S hS X hX} (u : M ⟶ N)
    (hMft : SheafOfModules.IsFiniteTypeOnSite M)
    (hM : HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj M)) :
    HasProperSupport B S hS hX hY f hf ((SheafOfModules.toSheaf _).obj
      (Abelian.image (C := Modules.{u, u} B S hS X hX) u)) := by
  obtain ⟨hcl, hp⟩ := hasProperSupport_of_epi B S hS hX hY f hf
    (Abelian.coimage.π (C := Modules.{u, u} B S hS X hX) u) hMft hM
  have he := supportOfSheaf_eq_of_iso B S hS ⟨X, hX⟩
    (Abelian.coimageIsoImage (C := Modules.{u, u} B S hS X hX) u)
  refine hasProperSupport_of_subset B S hS hX hY f hf ?_ (le_of_eq he.symm) ⟨hcl, hp⟩
  rw [← he]
  exact hcl

/-! ### Stacks 0CZK, part (2): the Serre subcategory -/

/-- **Stacks 0CZK, part (2).**  The coherent `𝒪_X`-modules whose support is proper over `Y`
form a Serre subcategory of the abelian category `Coh(𝒪_X)` of coherent `𝒪_X`-modules.

The property is `AlgebraicGeometry.Space.isCoherentProperOver`, the one cutting out the source
of equation 76.42.5.1, and the abelian structure on `Coh(𝒪_X)` is Stacks 07UC in the form
`AlgebraicGeometry.Space.coherentModules_abelian_of_closure`, which needs no locally Noetherian
hypothesis in this tree; the hypothesis of the source is therefore absent.

By Stacks 02MP it is enough to exhibit one object with the property and to show that the middle
term of an exact sequence whose outer terms have the property has it.  The zero module has
empty support.  For the exactness condition: the kernel `K` of `T.X₂ ⟶ T.X₃`, formed in the
ambient category of all `𝒪_X`-modules, is a quotient of `T.X₁` because the sequence is exact,
so it has support proper over `Y` by the quotient clause of part (1); the support of `T.X₂` is
contained in the union of the support of `K` and the support of `T.X₃`, by
`AlgebraicGeometry.Space.supportOfSheaf_subset_union_kernel`; and the support of `T.X₂` is
closed because a coherent module is of finite type, by Stacks 07TZ.  Stacks 0CZH and 0CZE then
finish, in the form `AlgebraicGeometry.Space.hasProperSupport_of_subset_union`. -/
@[stacks 0CZK "part (2), the Serre subcategory; the locally Noetherian hypothesis on Y is \
absent because the abelian structure on Coh(O_X) is Stacks 07UC in the hypothesis-free form \
`AlgebraicGeometry.Space.coherentModules_abelian_of_closure`"]
theorem isSerreClass_isCoherentProperOver (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f) :
    letI : Abelian (CoherentModules.{u, u} B S hS X hX) :=
      coherentModules_abelian_of_closure B S hS X hX
    (isCoherentProperOver B S hS hX hY f hf).IsSerreClass := by
  let : Abelian (CoherentModules.{u, u} B S hS X hX) :=
    coherentModules_abelian_of_closure B S hS X hX
  set P := isCoherentProperOver B S hS hX hY f hf
  have hker : ∀ {A D : CoherentModules.{u, u} B S hS X hX} (a : A ⟶ D),
      PreservesLimit (parallelPair a 0) (isCoherent.{u, u} B S hS X hX).ι :=
    fun a => ObjectProperty.preservesKernels_ι _ a
  have hcoker : ∀ {A D : CoherentModules.{u, u} B S hS X hX} (a : A ⟶ D),
      PreservesColimit (parallelPair a 0) (isCoherent.{u, u} B S hS X hX).ι :=
    fun a => ObjectProperty.preservesCokernels_ι _ a
  have _ : PreservesFiniteLimits (isCoherent.{u, u} B S hS X hX).ι :=
    Functor.preservesFiniteLimits_of_preservesKernels _
  have _ : PreservesFiniteColimits (isCoherent.{u, u} B S hS X hX).ι :=
    Functor.preservesFiniteColimits_of_preservesCokernels _
  refine (ObjectProperty.isSerreClass_iff_prop_X₂_of_exact P).2 ⟨⟨0, ?_⟩, ?_⟩
  · exact hasProperSupport_of_isZero B S hS hX hY f hf
      (Functor.map_isZero (isCoherent.{u, u} B S hS X hX).ι (isZero_zero _))
  · intro T hT h₁ h₃
    have hT' : (T.map (isCoherent.{u, u} B S hS X hX).ι).Exact :=
      hT.map (isCoherent.{u, u} B S hS X hX).ι
    have hzz : T.f.hom ≫ T.g.hom = 0 := (T.map (isCoherent.{u, u} B S hS X hX).ι).zero
    have _ : Epi (kernel.lift (C := Modules.{u, u} B S hS X hX) T.g.hom T.f.hom hzz) :=
      hT'.epi_kernelLift
    have hK : HasProperSupport B S hS hX hY f hf
        ((SheafOfModules.toSheaf _).obj
          (kernel (C := Modules.{u, u} B S hS X hX) T.g.hom)) :=
      hasProperSupport_of_epi B S hS hX hY f hf
        (kernel.lift (C := Modules.{u, u} B S hS X hX) T.g.hom T.f.hom hzz)
        (isFiniteTypeOnSite_of_isCoherentOnSite B S hS ⟨X, hX⟩ T.X₁.obj) h₁
    let : SheafOfModules.IsFiniteTypeOnSite T.X₂.obj :=
      isFiniteTypeOnSite_of_isCoherentOnSite B S hS ⟨X, hX⟩ T.X₂.obj
    exact hasProperSupport_of_subset_union B S hS hX hY f hf
      (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X hX T.X₂.obj)
      (supportOfSheaf_subset_union_kernel B S hS ⟨X, hX⟩ T.g.hom) hK h₃

end AlgebraicGeometry.Space

end
