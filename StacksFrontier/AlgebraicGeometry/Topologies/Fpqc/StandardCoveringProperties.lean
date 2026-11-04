module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Basic.Finite.Sigma
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement

/-!
# Closure properties of the standard fpqc coverings of an affine scheme

The standard fpqc coverings of an affine scheme are closed under the three operations which make
them the standard coverings of a topology on the affine schemes: an isomorphism onto an affine
scheme is a one-member standard fpqc covering, a standard fpqc covering of each member of a
standard fpqc covering assembles into a standard fpqc covering of the common target, and a
standard fpqc covering pulls back along a morphism of affine schemes to a standard fpqc
covering.

In each case the mathematical content is that the three defining conditions — finiteness of the
index, affineness of the sources, flatness of the members — survive the operation.  For an
isomorphism the source is affine because it is isomorphic to the affine target, and an
isomorphism is flat.  For the composition the index of the assembled family is the sigma type of
the indices, finite because each of its factors is, and its members are composites of flat
morphisms, hence flat.  For the base change the index is unchanged and flatness is preserved by
base change, while the affineness of the pulled back sources is the affineness of a fibre product
of affine schemes over an affine base, Stacks 01JQ; it is exactly this step that uses the
affineness of the new target.

Joint surjectivity in the three cases is, respectively, the surjectivity of an isomorphism, the
observation that a point of the target is hit through some member of the outer family and then
through some member of the inner family above it, and the surjectivity of the projection of a
fibre product onto a factor over the image points.

## Main results

* `AlgebraicGeometry.isStandardFpqcCovering_of_isIso`,
  `AlgebraicGeometry.IsStandardFpqcCovering.bind` and
  `AlgebraicGeometry.IsStandardFpqcCovering.pullback` — the three parts of Stacks 03LA, each
  stated of the family named in the source: the one-member family `{T' ⟶ T}` of an isomorphism,
  the family `{T_ij ⟶ T_i ⟶ T}` of composites, and the family `{T' ×_T T_i ⟶ T'}` of first
  projections.

## Main definitions

* `AlgebraicGeometry.Scheme.AffineCover.ofIsIso` — the one-member standard fpqc covering of an
  affine scheme given by an isomorphism onto it.
* `AlgebraicGeometry.Scheme.AffineCover.bind` — the standard fpqc covering assembled from a
  standard fpqc covering and a standard fpqc covering of each of its members.
* `AlgebraicGeometry.Scheme.AffineCover.pullback` — the standard fpqc covering obtained by base
  change along a morphism of affine schemes.

Each of these is the same family re-presented as an
`AlgebraicGeometry.Scheme.AffineCover`, and each carries the fpqc covering statements
`AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_ofIsIso`,
`AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_bind` and
`AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_pullback`.

## Implementation notes

The three parts of Stacks 03LA are stated of the predicate
`AlgebraicGeometry.IsStandardFpqcCovering` of Stacks 022F, which is where finiteness of the
index, affineness of the target and of the sources, flatness of the members and joint
surjectivity are all recorded; the statements here therefore carry the whole of the definition of
a standard fpqc covering, and they are about the families named in the source rather than about
re-presentations of them.  In part (2) the inner and the outer index types are allowed to lie in
different universes.

The three `AlgebraicGeometry.Scheme.AffineCover` constructions are retained because the rest of
the chapter consumes standard fpqc coverings in that shape, through
`AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_of_finite_affineCover`.  They are not the
statements of Stacks 03LA: the sources of an `AffineCover` are literally spectra of rings, so a
construction whose members are not already of that shape must name a ring, and rather than
computing it the construction transports the morphism along `AlgebraicGeometry.Scheme.isoSpec`.
The ring of the one-member family of an isomorphism `T' ⟶ T` is the ring of global sections of
`T'`, and the ring of the `i`-th member of a base change is the ring of global sections of the
fibre product.  The resulting member morphisms differ from the ones the source names by an
isomorphism of the source, which changes neither flatness nor the image, so the recorded
`simp` lemmas describe them in terms of `AlgebraicGeometry.Scheme.isoSpec` and the evident
morphism.  They therefore carry no `03LA` attribute: the covering set of Stacks 03LA is the three
theorems above, and these constructions are the scaffolding the chapter consumes.  Finiteness of
the index of an `AffineCover` is not part of its data, so for each construction it is recorded
separately.

The passage between the two shapes in either direction is
`AlgebraicGeometry.IsStandardFpqcCovering.of_finite_affineCover` and
`AlgebraicGeometry.IsStandardFpqcCovering.affineCover`.

## References

* [Stacks Project, Tag 01JQ](https://stacks.math.columbia.edu/tag/01JQ)
* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
* [Stacks Project, Tag 03LA](https://stacks.math.columbia.edu/tag/03LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-! ### The three parts of Stacks 03LA

Each part is stated of the family the source names, as a statement about the predicate
`AlgebraicGeometry.IsStandardFpqcCovering` of Stacks 022F. -/

/-- **Stacks 03LA (1).** If `T' ⟶ T` is an isomorphism onto an affine scheme, then the one-member
family `{T' ⟶ T}` is a standard fpqc covering: the source is affine because it is isomorphic to
the affine target, and an isomorphism is flat and surjective. -/
@[stacks 03LA "(1)"]
public theorem isStandardFpqcCovering_of_isIso {T T' : Scheme.{u}} [IsAffine T] (f : T' ⟶ T)
    [IsIso f] : IsStandardFpqcCovering (fun _ : PUnit.{v + 1} ↦ T') (fun _ ↦ f) where
  finite_index := inferInstance
  affine_target := ‹IsAffine T›
  affine_source _ := .of_isIso f
  flat _ := inferInstance
  jointly_surjective :=
    Set.eq_univ_iff_forall.mpr fun x ↦ Set.mem_iUnion.mpr ⟨PUnit.unit, f.surjective x⟩

/-- **Stacks 03LA (2).** If `{T_i ⟶ T}_{i ∈ I}` is a standard fpqc covering and
`{T_ij ⟶ T_i}_{j ∈ J i}` is a standard fpqc covering for every `i`, then the family of composites
`{T_ij ⟶ T}_{⟨i, j⟩ ∈ Σ i, J i}` is a standard fpqc covering.  Its index is the sigma type of the
indices, finite because each of its factors is; its members are composites of flat morphisms,
hence flat; and a point of `T` is hit through some member of the outer family and then through
some member of the inner family above it.  The inner and the outer index types may lie in
different universes. -/
@[stacks 03LA "(2)"]
public theorem IsStandardFpqcCovering.bind {T : Scheme.{u}} {I : Type v} {U : I → Scheme.{u}}
    {f : ∀ i, U i ⟶ T} (hf : IsStandardFpqcCovering U f) {J : I → Type w}
    {V : ∀ i, J i → Scheme.{u}} {g : ∀ i (j : J i), V i j ⟶ U i}
    (hg : ∀ i, IsStandardFpqcCovering (V i) (g i)) :
    IsStandardFpqcCovering (fun ij : Σ i, J i ↦ V ij.1 ij.2)
      (fun ij : Σ i, J i ↦ g ij.1 ij.2 ≫ f ij.1) where
  finite_index := by
    have hI : Finite I := hf.finite_index
    have hJ (i : I) : Finite (J i) := (hg i).finite_index
    infer_instance
  affine_target := hf.affine_target
  affine_source ij := (hg ij.1).affine_source ij.2
  flat ij := by
    have h₁ : Flat (g ij.1 ij.2) := (hg ij.1).flat ij.2
    have h₂ : Flat (f ij.1) := hf.flat ij.1
    infer_instance
  jointly_surjective := Set.eq_univ_iff_forall.mpr fun x ↦ by
    obtain ⟨i, y, hy⟩ := hf.exists_eq x
    obtain ⟨j, z, hz⟩ := (hg i).exists_eq y
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩

/-- **Stacks 03LA (3).** If `{T_i ⟶ T}_{i ∈ I}` is a standard fpqc covering and `T' ⟶ T` is a
morphism of affine schemes, then the family of first projections `{T' ×_T T_i ⟶ T'}_{i ∈ I}` is a
standard fpqc covering.  The index is unchanged, flatness is preserved by base change, each fibre
product is affine because it is a fibre product of affine schemes over an affine base, Stacks
01JQ, and a point of `T'` lies under a point of the fibre product over any point of `T_i` with the
same image in `T`. -/
@[stacks 03LA "(3)"]
public theorem IsStandardFpqcCovering.pullback {T : Scheme.{u}} {I : Type v} {U : I → Scheme.{u}}
    {f : ∀ i, U i ⟶ T} (hf : IsStandardFpqcCovering U f) {T' : Scheme.{u}} [IsAffine T']
    (g : T' ⟶ T) :
    IsStandardFpqcCovering (fun i ↦ Limits.pullback g (f i))
      (fun i ↦ Limits.pullback.fst g (f i)) where
  finite_index := hf.finite_index
  affine_target := ‹IsAffine T'›
  affine_source i := by
    have hT : IsAffine T := hf.affine_target
    have hU : IsAffine (U i) := hf.affine_source i
    infer_instance
  flat i := by
    have h : Flat (f i) := hf.flat i
    infer_instance
  jointly_surjective := Set.eq_univ_iff_forall.mpr fun x ↦ by
    obtain ⟨i, y, hy⟩ := hf.exists_eq (g x)
    obtain ⟨z, hz, -⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := g) (g := f i) x y hy.symm
    exact Set.mem_iUnion.mpr ⟨i, z, hz⟩

/-! ### The same three families as affine covers -/

/-- **Stacks 03LA (1)**, re-presented as an affine cover.  An isomorphism onto an affine scheme is
a standard fpqc covering with one member: the source is affine because it is isomorphic to the
affine target, so the isomorphism is a morphism out of the spectrum of the ring of global sections
of the source, and an isomorphism is flat and surjective.  The statement of Stacks 03LA (1) for
the family `{T' ⟶ T}` itself is `AlgebraicGeometry.isStandardFpqcCovering_of_isIso`. -/
public noncomputable def Scheme.AffineCover.ofIsIso {T T' : Scheme.{u}} [IsAffine T] (f : T' ⟶ T)
    [IsIso f] : T.AffineCover.{v} (@Flat.{u}) :=
  haveI : IsAffine T' := .of_isIso f
  { I₀ := PUnit.{v + 1}
    X _ := Γ(T', ⊤)
    f _ := T'.isoSpec.inv ≫ f
    idx _ := PUnit.unit
    covers x := by
      have : IsIso (T'.isoSpec.inv ≫ f) := inferInstance
      exact (T'.isoSpec.inv ≫ f).surjective x
    map_prop _ := by
      have : Flat f := inferInstance
      infer_instance }

/-- `AlgebraicGeometry.Scheme.AffineCover.ofIsIso` has a single member, indexed by `PUnit`. -/
@[simp]
public lemma Scheme.AffineCover.ofIsIso_I₀ {T T' : Scheme.{u}} [IsAffine T] (f : T' ⟶ T)
    [IsIso f] : (ofIsIso f : T.AffineCover.{v} (@Flat.{u})).I₀ = PUnit.{v + 1} :=
  rfl

/-- The single member of `AlgebraicGeometry.Scheme.AffineCover.ofIsIso` is the spectrum of the
ring of global sections of the source of the isomorphism; this is that ring. -/
@[simp]
public lemma Scheme.AffineCover.ofIsIso_X {T T' : Scheme.{u}} [IsAffine T] (f : T' ⟶ T) [IsIso f]
    (i : (ofIsIso f : T.AffineCover.{v} (@Flat.{u})).I₀) :
    (ofIsIso f : T.AffineCover.{v} (@Flat.{u})).X i = Γ(T', ⊤) :=
  rfl

/-- The single member of `AlgebraicGeometry.Scheme.AffineCover.ofIsIso` is the given isomorphism,
precomposed with the identification of the spectrum of the ring of global sections of its source
with that source.  The affineness of the source is the one the construction itself derives from
the affineness of the target. -/
@[simp]
public lemma Scheme.AffineCover.ofIsIso_f {T T' : Scheme.{u}} [IsAffine T]
    (f : T' ⟶ T) [IsIso f] (i : (ofIsIso f : T.AffineCover.{v} (@Flat.{u})).I₀) :
    (ofIsIso f : T.AffineCover.{v} (@Flat.{u})).f i =
      (@Scheme.isoSpec T' (.of_isIso f)).inv ≫ f :=
  rfl

/-- `AlgebraicGeometry.Scheme.AffineCover.ofIsIso` has finitely many members. -/
public instance Scheme.AffineCover.finite_I₀_ofIsIso {T T' : Scheme.{u}} [IsAffine T] (f : T' ⟶ T)
    [IsIso f] : Finite (ofIsIso f : T.AffineCover.{v} (@Flat.{u})).I₀ :=
  inferInstanceAs (Finite PUnit.{v + 1})

/-- The one-member family given by an isomorphism onto an affine scheme is an fpqc covering. -/
public lemma presieve₀_mem_fpqcPrecoverage_ofIsIso {T T' : Scheme.{u}} [IsAffine T] (f : T' ⟶ T)
    [IsIso f] :
    (Scheme.AffineCover.ofIsIso f : T.AffineCover.{v} (@Flat.{u})).cover.presieve₀ ∈
      Scheme.fpqcPrecoverage T :=
  presieve₀_mem_fpqcPrecoverage_of_finite_affineCover _

/-- **Stacks 03LA (2)**, re-presented as an affine cover.  A standard fpqc covering of each member
of a standard fpqc covering of an affine scheme assembles into a standard fpqc covering of that
scheme.  The index of the assembled family is the sigma type of the indices, its `⟨i, j⟩`-th
member is the `j`-th member of the `i`-th inner family followed by the `i`-th member of the outer
family, and no affineness hypothesis on the intermediate schemes is needed because the members of
an affine cover are spectra of rings.  The statement of Stacks 03LA (2) for the family of
composites itself, with the inner and the outer index types in arbitrary universes, is
`AlgebraicGeometry.IsStandardFpqcCovering.bind`. -/
public noncomputable def Scheme.AffineCover.bind {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u}))
    (𝒱 : ∀ i : 𝒰.I₀, (Spec (𝒰.X i)).AffineCover.{v} (@Flat.{u})) :
    T.AffineCover.{v} (@Flat.{u}) where
  I₀ := Σ i : 𝒰.I₀, (𝒱 i).I₀
  X ij := (𝒱 ij.1).X ij.2
  f ij := (𝒱 ij.1).f ij.2 ≫ 𝒰.f ij.1
  idx x := ⟨𝒰.idx x, (𝒱 (𝒰.idx x)).idx (𝒰.covers x).choose⟩
  covers x := by
    obtain ⟨z, hz⟩ := (𝒱 (𝒰.idx x)).covers (𝒰.covers x).choose
    refine ⟨z, ?_⟩
    simp only [Scheme.Hom.comp_apply]
    rw [hz, (𝒰.covers x).choose_spec]
  map_prop ij := by
    have h₁ : Flat ((𝒱 ij.1).f ij.2) := (𝒱 ij.1).map_prop ij.2
    have h₂ : Flat (𝒰.f ij.1) := 𝒰.map_prop ij.1
    infer_instance

/-- The members of `AlgebraicGeometry.Scheme.AffineCover.bind` are indexed by the sigma type of
the outer and the inner indices. -/
@[simp]
public lemma Scheme.AffineCover.bind_I₀ {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u}))
    (𝒱 : ∀ i : 𝒰.I₀, (Spec (𝒰.X i)).AffineCover.{v} (@Flat.{u})) :
    (𝒰.bind 𝒱).I₀ = Σ i : 𝒰.I₀, (𝒱 i).I₀ :=
  rfl

/-- The `⟨i, j⟩`-th member of `AlgebraicGeometry.Scheme.AffineCover.bind` is the `j`-th member of
the `i`-th inner family. -/
@[simp]
public lemma Scheme.AffineCover.bind_X {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u}))
    (𝒱 : ∀ i : 𝒰.I₀, (Spec (𝒰.X i)).AffineCover.{v} (@Flat.{u}))
    (i : 𝒰.I₀) (j : (𝒱 i).I₀) : (𝒰.bind 𝒱).X ⟨i, j⟩ = (𝒱 i).X j :=
  rfl

/-- The members of `AlgebraicGeometry.Scheme.AffineCover.bind` are the composites of a member of
an inner family with the member of the outer family above which it lies. -/
@[simp]
public lemma Scheme.AffineCover.bind_f {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u}))
    (𝒱 : ∀ i : 𝒰.I₀, (Spec (𝒰.X i)).AffineCover.{v} (@Flat.{u}))
    (i : 𝒰.I₀) (j : (𝒱 i).I₀) : (𝒰.bind 𝒱).f ⟨i, j⟩ = (𝒱 i).f j ≫ 𝒰.f i :=
  rfl

/-- `AlgebraicGeometry.Scheme.AffineCover.bind` of a finite family of finite families has finitely
many members. -/
public instance Scheme.AffineCover.finite_I₀_bind {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u})) [Finite 𝒰.I₀]
    (𝒱 : ∀ i : 𝒰.I₀, (Spec (𝒰.X i)).AffineCover.{v} (@Flat.{u}))
    [∀ i : 𝒰.I₀, Finite (𝒱 i).I₀] : Finite (𝒰.bind 𝒱).I₀ :=
  inferInstanceAs (Finite (Σ i : 𝒰.I₀, (𝒱 i).I₀))

/-- The family assembled from a standard fpqc covering and a standard fpqc covering of each of its
members is an fpqc covering. -/
public lemma presieve₀_mem_fpqcPrecoverage_bind {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u})) [Finite 𝒰.I₀]
    (𝒱 : ∀ i : 𝒰.I₀, (Spec (𝒰.X i)).AffineCover.{v} (@Flat.{u}))
    [∀ i : 𝒰.I₀, Finite (𝒱 i).I₀] :
    (𝒰.bind 𝒱).cover.presieve₀ ∈ Scheme.fpqcPrecoverage T :=
  presieve₀_mem_fpqcPrecoverage_of_finite_affineCover _

/-- **Stacks 03LA (3)**, re-presented as an affine cover.  A standard fpqc covering of an affine
scheme pulls back, along a morphism of affine schemes, to a standard fpqc covering of the new
target.  The index is unchanged, the `i`-th member is the second projection of the fibre product
of the `i`-th member with the given morphism, and that fibre product is affine because it is a
fibre product of affine schemes over an affine base, Stacks 01JQ; this is the step that uses the
affineness of the new target.  The statement of Stacks 03LA (3) for the family of projections
itself is `AlgebraicGeometry.IsStandardFpqcCovering.pullback`. -/
public noncomputable def Scheme.AffineCover.pullback {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u})) {T' : Scheme.{u}} [IsAffine T'] (g : T' ⟶ T) :
    T'.AffineCover.{v} (@Flat.{u}) where
  I₀ := 𝒰.I₀
  X i := Γ(Limits.pullback (𝒰.f i) g, ⊤)
  f i := (Limits.pullback (𝒰.f i) g).isoSpec.inv ≫ Limits.pullback.snd (𝒰.f i) g
  idx x := 𝒰.idx (g x)
  covers x := by
    obtain ⟨y, hy⟩ := 𝒰.covers (g x)
    obtain ⟨z, -, hz⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f (𝒰.idx (g x))) (g := g) y x hy
    rw [mem_range_iff_of_surjective _ (Limits.pullback.snd (𝒰.f (𝒰.idx (g x))) g)
      (Limits.pullback (𝒰.f (𝒰.idx (g x))) g).isoSpec.inv rfl]
    exact ⟨z, hz⟩
  map_prop i := by
    have h : Flat (𝒰.f i) := 𝒰.map_prop i
    infer_instance

/-- `AlgebraicGeometry.Scheme.AffineCover.pullback` keeps the index of the family it pulls
back. -/
@[simp]
public lemma Scheme.AffineCover.pullback_I₀ {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u})) {T' : Scheme.{u}} [IsAffine T'] (g : T' ⟶ T) :
    (𝒰.pullback g).I₀ = 𝒰.I₀ :=
  rfl

/-- The `i`-th member of `AlgebraicGeometry.Scheme.AffineCover.pullback` is the spectrum of the
ring of global sections of the fibre product of the `i`-th member with the given morphism; this
is that ring. -/
@[simp]
public lemma Scheme.AffineCover.pullback_X {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u})) {T' : Scheme.{u}} [IsAffine T'] (g : T' ⟶ T) (i : 𝒰.I₀) :
    (𝒰.pullback g).X i = Γ(Limits.pullback (𝒰.f i) g, ⊤) :=
  rfl

/-- The members of `AlgebraicGeometry.Scheme.AffineCover.pullback` are the second projections of
the fibre products, precomposed with the identification of the spectrum of the ring of global
sections of a fibre product with that fibre product. -/
@[simp]
public lemma Scheme.AffineCover.pullback_f {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u})) {T' : Scheme.{u}} [IsAffine T'] (g : T' ⟶ T) (i : 𝒰.I₀) :
    (𝒰.pullback g).f i =
      (Limits.pullback (𝒰.f i) g).isoSpec.inv ≫ Limits.pullback.snd (𝒰.f i) g :=
  rfl

/-- The pullback of a finite affine cover has finitely many members. -/
public instance Scheme.AffineCover.finite_I₀_pullback {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u})) [Finite 𝒰.I₀] {T' : Scheme.{u}} [IsAffine T']
    (g : T' ⟶ T) : Finite (𝒰.pullback g).I₀ :=
  inferInstanceAs (Finite 𝒰.I₀)

/-- The base change of a standard fpqc covering along a morphism of affine schemes is an fpqc
covering. -/
public lemma presieve₀_mem_fpqcPrecoverage_pullback {T : Scheme.{u}} [IsAffine T]
    (𝒰 : T.AffineCover.{v} (@Flat.{u})) [Finite 𝒰.I₀] {T' : Scheme.{u}} [IsAffine T']
    (g : T' ⟶ T) :
    (𝒰.pullback g).cover.presieve₀ ∈ Scheme.fpqcPrecoverage T' :=
  presieve₀_mem_fpqcPrecoverage_of_finite_affineCover _

end AlgebraicGeometry

end
