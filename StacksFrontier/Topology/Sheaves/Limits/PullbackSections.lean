module

public import StacksFrontier.Topology.Spectral.InverseLimits
public import StacksFrontier.Topology.Sheaves.Limits.GermPullback
public import StacksFrontier.Topology.Sheaves.Limits.CofilteredSliceLimit
public import StacksFrontier.Topology.Spectral.LimitOpenDescent

/-!
# Sections of a pullback sheaf on a cofiltered limit of spectral spaces

Let `J` be a cofiltered index category and `D : SpectralDiagram J` a diagram `j ↦ X_j` of
spectral spaces whose transition maps `f_a : X_j → X_i` are spectral.  Write `X = lim X_j` with
projections `p_j : X → X_j`.  Fix `i : J`, a sheaf of sets `𝒢` on `X_i`, and a quasi-compact
open `U ⊆ X_i`.

Every object `a : j ⟶ i` of the slice `Over i` gives the set of sections `(f_a⁻¹𝒢)(f_a⁻¹ U)`, and a
morphism `b` of the slice gives the pullback map along `f_b`; this is the functor
`SpectralDiagram.sliceFunctor`. Pullback along `p_j` assembles these into a cocone with vertex
`(p_i⁻¹𝒢)(p_i⁻¹ U)`, and `SpectralDiagram.canonicalMap` is the induced map out of the colimit,
which is bijective. Pullback sheaves are taken in the germ model `GermPullback.sheaf`.

## Main definitions

* `SpectralDiagram.sliceFunctor`: the diagram `a ↦ (f_a⁻¹𝒢)(f_a⁻¹ U)` over `(Over i)ᵒᵖ`.
* `SpectralDiagram.canonicalMap`: the canonical map
  `colim_{a : j → i} (f_a⁻¹𝒢)(f_a⁻¹ U) → (p_i⁻¹𝒢)(p_i⁻¹ U)`.
* `SpectralDiagram.germAt`: the germ, at a point of a stage, of a section of `𝒢` on an open of
  `X_i` containing the image of that point.

## Main results

* `SpectralDiagram.bijective_canonicalMap`: the canonical map is bijective.
* `SpectralDiagram.injective_canonicalMap`: the canonical map is injective.
* `SpectralDiagram.surjective_canonicalMap`: the canonical map is surjective.
* `SpectralDiagram.exists_mapFun_eq_of_projFun_eq`: two sections of `f_a⁻¹𝒢` over a
  quasi-compact open of a stage whose germs agree at every point of `X` over that open already
  agree at some further stage.
* `SpectralDiagram.exists_finite_compact_repr`: a section of `p_i⁻¹𝒢` over `p_i⁻¹ U` is given
  germwise, on the members of a finite covering of `p_i⁻¹ U` by quasi-compact opens, by sections
  of `𝒢` over quasi-compact opens of `X_i`.
* `SpectralDiagram.exists_stage_covering`: such a covering descends to a single stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe v u
universe v'

noncomputable section

namespace SpectralDiagram

variable {J : Type v} [Category.{v'} J] [IsCofiltered J] (D : SpectralDiagram.{v, u} J)

attribute [local instance] SpectralDiagram.isSpectralSpace

/-! ### Transition maps as bare functions -/

/-- A transition map of the diagram, as a bare function on underlying spaces. -/
def mapFun {j i : J} (a : j ⟶ i) : D.F.obj j → D.F.obj i := ConcreteCategory.hom (D.F.map a)

/-- A transition map of the diagram is continuous. -/
lemma mapFun_continuous {j i : J} (a : j ⟶ i) : Continuous (D.mapFun a) :=
  (D.F.map a).hom.continuous

/-- The transition maps compose as bare functions: `f_{a ≫ b} = f_b ∘ f_a`, pointwise. -/
lemma mapFun_comp {k j i : J} (a : k ⟶ j) (b : j ⟶ i) (z : D.F.obj k) :
    D.mapFun (a ≫ b) z = D.mapFun b (D.mapFun a z) := by
  unfold mapFun
  rw [D.F.map_comp, ConcreteCategory.comp_apply]

/-- The transition map along an identity morphism is the identity function. -/
lemma mapFun_id {j : J} (z : D.F.obj j) : D.mapFun (𝟙 j) z = z := by
  unfold mapFun
  rw [D.F.map_id, ConcreteCategory.id_apply]

/-- A point lies in the preimage of an open `V` under a transition map exactly when its image under
`mapFun` lies in `V`. -/
lemma mem_map_mapFun {j i : J} (a : j ⟶ i) {V : Opens (D.F.obj i)} {z : D.F.obj j} :
    z ∈ (Opens.map (D.F.map a)).obj V ↔ D.mapFun a z ∈ V :=
  Iff.rfl

/-- Applying a transition map of the diagram to a point is `mapFun`. -/
lemma map_apply_eq_mapFun {j i : J} (a : j ⟶ i) (z : D.F.obj j) : D.F.map a z = D.mapFun a z :=
  rfl

/-- The coordinates of a point of the limit are compatible with the transition maps: for
`a : j ⟶ i`, the `i`-th coordinate of `x` is the image of its `j`-th coordinate under `f_a`. -/
lemma projFun_eq_mapFun {j i : J} (a : j ⟶ i) (x : D.invLimit) :
    D.projFun i x = D.mapFun a (D.projFun j x) := D.projFun_comp a x

variable {i : J} (U : Opens (D.F.obj i))

/-! ### The preimages of `U` -/

/-- The preimage of `U` at the stage `A.left`, for `A` an object of the slice over `i`. -/
def slicePre (A : Over i) : Opens (D.F.obj A.left) := (Opens.map (D.F.map A.hom)).obj U

/-- A point of the stage `A.left` lies in `slicePre U A` exactly when its image under the
transition map `f_{A.hom}` lies in `U`. -/
@[simp]
lemma mem_slicePre {A : Over i} {z : D.F.obj A.left} :
    z ∈ D.slicePre U A ↔ D.mapFun A.hom z ∈ U := Iff.rfl

/-- The preimage of `U` in the limit `X`. -/
def limPre : Opens D.invLimit := (Opens.map (D.proj i)).obj U

/-- A point of the limit lies in `limPre U` exactly when its `i`-th coordinate lies in `U`. -/
@[simp]
lemma mem_limPre {x : D.invLimit} : x ∈ D.limPre U ↔ D.projFun i x ∈ U := Iff.rfl

/-- For a morphism of the slice over `i`, the transition maps compose on underlying spaces. -/
lemma slice_comp {A A' : Over i} (f : A' ⟶ A) (z : D.F.obj A'.left) :
    D.mapFun A'.hom z = D.mapFun A.hom (D.mapFun f.left z) := by
  rw [← D.mapFun_comp, Over.w]

/-- A morphism `f : A' ⟶ A` of the slice over `i` carries the preimage of `U` at the stage
`A'.left` into the preimage of `U` at the stage `A.left`. -/
lemma slice_mem {A A' : Over i} (f : A' ⟶ A) (z : D.slicePre U A') :
    D.mapFun f.left z.1 ∈ D.slicePre U A := by
  rw [mem_slicePre, ← D.slice_comp f]
  exact z.2

/-- The `A.left`-coordinate of a point of the limit lying in `limPre U` lies in the preimage of
`U` at the stage `A.left`. -/
lemma proj_mem {A : Over i} (x : D.limPre U) : D.projFun A.left x.1 ∈ D.slicePre U A := by
  rw [mem_slicePre, ← D.projFun_eq_mapFun A.hom]
  exact x.2

/-! ### The diagram over the slice, and the canonical map -/

variable (𝒢 : (D.F.obj i).Sheaf (Type max v u))

/-- The diagram of pullback sections over the slice `Over i`: the object `a : j ⟶ i` is sent to
the sections of `f_a⁻¹𝒢` over `f_a⁻¹(U)`, and a morphism `b` of the slice to pullback of
sections along `f_b`. -/
def sliceFunctor : (Over i)ᵒᵖ ⥤ Type max v u where
  obj A := (GermPullback.sheaf (D.mapFun A.unop.hom) 𝒢.presheaf).presheaf.obj
    (op (D.slicePre U A.unop))
  map {_ _} f := ↾fun σ ↦ GermPullback.comap (𝒢 := 𝒢.presheaf)
    (D.mapFun_continuous f.unop.left) (fun z ↦ D.slice_comp f.unop z)
    (fun z ↦ D.slice_mem U f.unop z) σ
  map_id A := by
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    simp only [TypeCat.ofHom_apply, ConcreteCategory.id_apply]
    refine GermPullback.ext fun z ↦ ?_
    rw [GermPullback.comap_val]
    exact congrArg σ.1 (Subtype.ext (D.mapFun_id z.1))
  map_comp {_ _ _} f g := by
    refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
    simp only [TypeCat.ofHom_apply, ConcreteCategory.comp_apply]
    refine Eq.symm ((GermPullback.comap_comp _ _ _ _ _ _ σ).trans ?_)
    exact GermPullback.comap_congr _ _ _ _ _ _
      (fun z ↦ (D.mapFun_comp g.unop.left f.unop.left z).symm) σ

/-- Pullback of sections along a morphism `f` of the slice is computed pointwise: the image of `σ`
takes at `z` the value `σ` takes at the image of `z` under `f`. -/
@[simp]
lemma sliceFunctor_map_val {A A' : (Over i)ᵒᵖ} (f : A ⟶ A')
    (σ : (D.sliceFunctor U 𝒢).obj A) (z : D.slicePre U A'.unop) :
    (((D.sliceFunctor U 𝒢).map f) σ).1 z =
      σ.1 ⟨D.mapFun f.unop.left z.1, D.slice_mem U f.unop z⟩ := rfl

/-- The sections of `p_i⁻¹𝒢` over `p_i⁻¹(U)`: the target of the canonical map. -/
abbrev limSections : Type max v u :=
  (GermPullback.sheaf (D.projFun i) 𝒢.presheaf).presheaf.obj (op (D.limPre U))

/-- Pullback of sections from the stage `A.left` to the limit `X`, along the projection
`p_{A.left}`. -/
def toLim (A : Over i) (σ : (D.sliceFunctor U 𝒢).obj (op A)) : D.limSections U 𝒢 :=
  GermPullback.comap (𝒢 := 𝒢.presheaf) (D.projFun_continuous A.left)
    (fun x ↦ D.projFun_eq_mapFun A.hom x) (fun x ↦ D.proj_mem U x) σ

/-- The pullback to the limit of a section over the stage `A.left` takes at a point `x` of
`limPre U` the value that section takes at the `A.left`-coordinate of `x`. -/
@[simp]
lemma toLim_val (A : Over i) (σ : (D.sliceFunctor U 𝒢).obj (op A)) (x : D.limPre U) :
    (D.toLim U 𝒢 A σ).1 x = σ.1 ⟨D.projFun A.left x.1, D.proj_mem U x⟩ := rfl

/-- The cocone on the slice diagram given by pulling sections back to the limit `X` along the
projections. -/
def sliceCocone : Cocone (D.sliceFunctor U 𝒢) where
  pt := D.limSections U 𝒢
  ι :=
    { app A := ↾D.toLim U 𝒢 A.unop
      naturality := by
        intro A A' f
        refine ConcreteCategory.hom_ext _ _ fun σ ↦ ?_
        refine GermPullback.ext fun x ↦ ?_
        simp only [TypeCat.ofHom_apply, ConcreteCategory.comp_apply, Functor.const_obj_map,
          toLim_val, sliceFunctor_map_val]
        exact congrArg σ.1 (Subtype.ext (D.projFun_eq_mapFun f.unop.left x.1).symm) }

/-- The canonical map `colim_{a : j → i} (f_a⁻¹𝒢)(f_a⁻¹ U) → (p_i⁻¹𝒢)(p_i⁻¹ U)`, induced by pulling
sections back to the limit along the projections. -/
@[stacks 0A32 "the canonical map"]
def canonicalMap [UnivLE.{max v v', max v u}] :
    colimit (D.sliceFunctor U 𝒢) ⟶ (D.sliceCocone U 𝒢).pt :=
  colimit.desc _ (D.sliceCocone U 𝒢)

/-- The canonical map agrees on the image of the colimit inclusion at `A` with the leg of the
cocone `sliceCocone` at `A`. -/
@[simp]
lemma canonicalMap_ι [UnivLE.{max v v', max v u}] (A : (Over i)ᵒᵖ)
    (σ : (D.sliceFunctor U 𝒢).obj A) :
    D.canonicalMap U 𝒢 (colimit.ι (D.sliceFunctor U 𝒢) A σ) =
      (D.sliceCocone U 𝒢).ι.app A σ := by
  rw [canonicalMap, ← ConcreteCategory.comp_apply, colimit.ι_desc]

/-- The canonical map sends the class of a section over the stage `a : j ⟶ i` to its pullback
along `p_j`. -/
lemma canonicalMap_ι_apply [UnivLE.{max v v', max v u}] (A : Over i)
    (σ : (D.sliceFunctor U 𝒢).obj (op A)) :
    D.canonicalMap U 𝒢 (colimit.ι (D.sliceFunctor U 𝒢) (op A) σ) = D.toLim U 𝒢 A σ :=
  D.canonicalMap_ι U 𝒢 (op A) σ

/-! ### Injectivity of the canonical map -/

/-- The diagram of a `SpectralDiagram` is a spectral diagram: its objects are spectral spaces and
its transition maps are spectral maps. -/
lemma isSpectralDiagram : SpectralLimits.IsSpectralDiagram D.F :=
  ⟨D.isSpectralSpace, fun {_ _} a ↦ D.isSpectralMap a⟩

/-- A transition map of the diagram is spectral, as a bare function on underlying spaces. -/
lemma isSpectralMap_mapFun {j k : J} (a : j ⟶ k) : IsSpectralMap (D.mapFun a) :=
  D.isSpectralMap a

/-- A compatible family of points of the diagram is the family of coordinates of a point of the
inverse limit. -/
lemma exists_projFun_eq (x : ∀ m : J, D.F.obj m) (hx : x ∈ SpectralLimits.limitSet D.F) :
    ∃ w : D.invLimit, ∀ m : J, D.projFun m w = x m := by
  let t : LimitCone D.F := ⟨TopCat.limitCone D.F, TopCat.limitConeIsLimit D.F⟩
  refine ⟨(limit.isoLimitCone t).inv ⟨x, fun {_ _} c ↦ hx c⟩, fun m ↦ ?_⟩
  have h := ConcreteCategory.comp_apply (limit.isoLimitCone t).inv (limit.π D.F m)
    ⟨x, fun {_ _} c ↦ hx c⟩
  rw [limit.isoLimitCone_inv_π] at h
  unfold projFun proj invLimit
  rw [← h]
  rfl

/-- The preimage of a quasi-compact open `U` at any stage of the slice over `i` is again
quasi-compact, the transition maps being spectral. -/
lemma isCompact_slicePre (hU : IsCompact (U : Set (D.F.obj i))) (A : Over i) :
    IsCompact (D.slicePre U A : Set (D.F.obj A.left)) :=
  (D.isSpectralMap_mapFun A.hom).isCompact_preimage_of_isOpen U.isOpen hU

private lemma isClosed_inter_constructible {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : @IsClosed X (constructibleTopology X) s)
    (ht : @IsClosed X (constructibleTopology X) t) :
    @IsClosed X (constructibleTopology X) (s ∩ t) :=
  @IsClosed.inter X s t (constructibleTopology X) hs ht

/-- A point of the limit whose `j`-th coordinate lies in a quasi-compact open `W ⊆ X_j` but outside
an open `S`, given that at every stage over `j` some point lying over `W` lies outside `S`. -/
lemma exists_projFun_mem_diff_of_forall_nonempty {j : J} {W S : Set (D.F.obj j)} (hWo : IsOpen W)
    (hWc : IsCompact W) (hS : IsOpen S)
    (hne : ∀ (m : J) (c : m ⟶ j), (D.mapFun c ⁻¹' (W \ S)).Nonempty) :
    ∃ x : D.invLimit, D.projFun j x ∈ W \ S := by
  have hcl : ∀ B : Over j, @IsClosed (D.F.obj B.left) (constructibleTopology (D.F.obj B.left))
      (D.mapFun B.hom ⁻¹' (W \ S)) := by
    intro B
    rw [Set.sdiff_eq, Set.preimage_inter]
    refine isClosed_inter_constructible ?_ ?_
    · exact (((D.isSpectralMap_mapFun B.hom).isCompact_preimage_of_isOpen hWo
        hWc).isClopen_constructibleTopology (hWo.preimage (D.mapFun_continuous B.hom))).1
    · exact (hS.isClosed_compl.preimage
        (D.mapFun_continuous B.hom)).isClosed_constructibleTopology
  have hcomp : ∀ {B B' : Over j} (f : B' ⟶ B),
      D.F.map f.left '' (D.mapFun B'.hom ⁻¹' (W \ S)) ⊆ D.mapFun B.hom ⁻¹' (W \ S) := by
    rintro B B' f z ⟨y, hy, rfl⟩
    rw [Set.mem_preimage, D.map_apply_eq_mapFun, ← D.mapFun_comp, Over.w]
    exact hy
  obtain ⟨x, hx_lim, hxZ⟩ := SpectralLimits.nonempty_limitSet_inter_over D.isSpectralDiagram j
    (fun B ↦ D.mapFun B.hom ⁻¹' (W \ S)) (fun B ↦ hne B.left B.hom) hcl hcomp
  have hx0 : D.mapFun (𝟙 j) (x j) ∈ W \ S := hxZ (Over.mk (𝟙 j))
  rw [D.mapFun_id] at hx0
  obtain ⟨w, hw⟩ := D.exists_projFun_eq x hx_lim
  exact ⟨w, by rw [hw j]; exact hx0⟩

/-- Two sections of `f_a⁻¹𝒢` over a quasi-compact open `W ⊆ X_j` whose germs agree at every point
of `X` lying over `W` already agree at every point lying over `W` at some stage `c : m ⟶ j`. -/
theorem exists_mapFun_eq_of_projFun_eq {j : J} (a : j ⟶ i) (W : Opens (D.F.obj j))
    (hW : IsCompact (W : Set (D.F.obj j)))
    (σ τ : (GermPullback.sheaf (D.mapFun a) 𝒢.presheaf).presheaf.obj (op W))
    (h : ∀ (x : D.invLimit) (hx : D.projFun j x ∈ W),
      σ.1 ⟨D.projFun j x, hx⟩ = τ.1 ⟨D.projFun j x, hx⟩) :
    ∃ (m : J) (c : m ⟶ j), ∀ (z : D.F.obj m) (hz : D.mapFun c z ∈ W),
      σ.1 ⟨D.mapFun c z, hz⟩ = τ.1 ⟨D.mapFun c z, hz⟩ := by
  by_contra hcon
  simp only [not_exists] at hcon
  obtain ⟨x, hxW, hxS⟩ := D.exists_projFun_mem_diff_of_forall_nonempty W.isOpen hW
    (GermPullback.isOpen_agreeSet (D.mapFun_continuous a) σ τ) fun m c ↦ by
      obtain ⟨z, hz, hneq⟩ := not_forall₂.mp (hcon m c)
      exact ⟨z, hz, fun ⟨_, heq⟩ ↦ hneq heq⟩
  exact hxS ⟨hxW, h x hxW⟩

/-- If two sections of `f_a⁻¹𝒢` over `f_a⁻¹(U)` have the same pullback to the limit, then they
already agree after pulling back to some stage over `a`. -/
theorem exists_map_eq_of_toLim_eq (hU : IsCompact (U : Set (D.F.obj i))) (A : Over i)
    (σ τ : (D.sliceFunctor U 𝒢).obj (op A)) (h : D.toLim U 𝒢 A σ = D.toLim U 𝒢 A τ) :
    ∃ (B : Over i) (f : B ⟶ A),
      (D.sliceFunctor U 𝒢).map f.op σ = (D.sliceFunctor U 𝒢).map f.op τ := by
  have key (x : D.invLimit) (hx : D.projFun A.left x ∈ D.slicePre U A) :
      σ.1 ⟨D.projFun A.left x, hx⟩ = τ.1 ⟨D.projFun A.left x, hx⟩ := by
    have hxU : x ∈ D.limPre U := by
      rw [mem_limPre, D.projFun_eq_mapFun A.hom]
      exact hx
    exact congrArg (fun s ↦ s.1 ⟨x, hxU⟩) h
  obtain ⟨m, c, hc⟩ := D.exists_mapFun_eq_of_projFun_eq 𝒢 A.hom (D.slicePre U A)
    (D.isCompact_slicePre U hU A) σ τ key
  exact ⟨Over.mk (c ≫ A.hom), Over.homMk c, GermPullback.ext fun z ↦ hc z.1 _⟩

/-- The class in the colimit of a section over a stage of the slice is unchanged by pulling it back
further down the slice. -/
lemma colimit_ι_map [UnivLE.{max v v', max v u}] (A B : (Over i)ᵒᵖ) (f : A ⟶ B)
    (σ : (D.sliceFunctor U 𝒢).obj A) :
    colimit.ι (D.sliceFunctor U 𝒢) B ((D.sliceFunctor U 𝒢).map f σ) =
      colimit.ι (D.sliceFunctor U 𝒢) A σ := by
  rw [← ConcreteCategory.comp_apply, colimit.w]

/-- The canonical map is injective when `U` is quasi-compact. -/
theorem injective_canonicalMap [UnivLE.{max v v', max v u}] (hU : IsCompact (U : Set (D.F.obj i))) :
    Function.Injective (D.canonicalMap U 𝒢) := by
  intro p q hpq
  obtain ⟨A₁, σ₁, h₁⟩ :=
    Types.jointly_surjective_of_isColimit (colimit.isColimit (D.sliceFunctor U 𝒢)) p
  obtain ⟨A₂, σ₂, h₂⟩ :=
    Types.jointly_surjective_of_isColimit (colimit.isColimit (D.sliceFunctor U 𝒢)) q
  have hp : colimit.ι (D.sliceFunctor U 𝒢) (IsFiltered.max A₁ A₂)
      ((D.sliceFunctor U 𝒢).map (IsFiltered.leftToMax A₁ A₂) σ₁) = p :=
    (D.colimit_ι_map U 𝒢 _ _ _ σ₁).trans h₁
  have hq : colimit.ι (D.sliceFunctor U 𝒢) (IsFiltered.max A₁ A₂)
      ((D.sliceFunctor U 𝒢).map (IsFiltered.rightToMax A₁ A₂) σ₂) = q :=
    (D.colimit_ι_map U 𝒢 _ _ _ σ₂).trans h₂
  have htoLim : D.toLim U 𝒢 (IsFiltered.max A₁ A₂).unop
        ((D.sliceFunctor U 𝒢).map (IsFiltered.leftToMax A₁ A₂) σ₁) =
      D.toLim U 𝒢 (IsFiltered.max A₁ A₂).unop
        ((D.sliceFunctor U 𝒢).map (IsFiltered.rightToMax A₁ A₂) σ₂) := by
    rw [← D.canonicalMap_ι_apply U 𝒢, ← D.canonicalMap_ι_apply U 𝒢, hp, hq]
    exact hpq
  obtain ⟨B, f, hf⟩ :=
    D.exists_map_eq_of_toLim_eq U 𝒢 hU (IsFiltered.max A₁ A₂).unop _ _ htoLim
  rw [← hp, ← hq, ← D.colimit_ι_map U 𝒢 _ (op B) f.op, ← D.colimit_ι_map U 𝒢 _ (op B) f.op, hf]

/-! ### Common refinements in the index category -/

/-- Finitely many morphisms with target `B`, together with one distinguished such morphism, admit a
common refinement: a single morphism to `B` factoring through each of them. -/
private lemma exists_common_factoring {ι : Type*} [Finite ι] {B A : J} (m : ι → J)
    (γ : ∀ l, m l ⟶ B) (γ₀ : A ⟶ B) :
    ∃ (C : J) (d : C ⟶ B), (∃ u : C ⟶ A, u ≫ γ₀ = d) ∧ ∀ l, ∃ u : C ⟶ m l, u ≫ γ l = d := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists
    (insert (Over.mk γ₀) (Finset.image (fun l ↦ Over.mk (γ l)) Finset.univ) : Finset (Over B))
  refine ⟨S.left, S.hom, ?_, fun l ↦ ?_⟩
  · obtain ⟨f⟩ := hS (Finset.mem_insert_self _ _)
    exact ⟨f.left, Over.w f⟩
  · obtain ⟨f⟩ := hS (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l)))
    exact ⟨f.left, Over.w f⟩

/-- A finite family of objects, together with one distinguished object, has a common lower bound
in the cofiltered index category. -/
private lemma exists_common_lowerBound {ι : Type*} [Finite ι] (m : ι → J) (A : J) :
    ∃ C : J, Nonempty (C ⟶ A) ∧ ∀ l, Nonempty (C ⟶ m l) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists (insert A (Finset.image m Finset.univ) : Finset J)
  exact ⟨S, hS (Finset.mem_insert_self _ _),
    fun l ↦ hS (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l)))⟩

/-- Transition maps compose pointwise along a factorization `u ≫ γ = d`. -/
private lemma mapFun_mapFun_eq {k m j : J} {u : k ⟶ m} {γ : m ⟶ j} {d : k ⟶ j} (hu : u ≫ γ = d)
    (z : D.F.obj k) : D.mapFun γ (D.mapFun u z) = D.mapFun d z := by
  rw [← D.mapFun_comp, hu]

/-- The preimage in the limit of a set at a stage `X_j` is its preimage under `f_a` at `X_i`. -/
private lemma preimage_projFun_preimage_mapFun {j : J} (a : j ⟶ i) (S : Set (D.F.obj i)) :
    D.projFun j ⁻¹' (D.mapFun a ⁻¹' S) = D.projFun i ⁻¹' S :=
  Set.ext fun x ↦ by simp only [Set.mem_preimage, ← D.projFun_eq_mapFun a x]

/-! ### Germs of a local section along a stage -/

/-- The germ, at a point `y` of the stage `X_j`, of a section `t` of `𝒢` on an open of `X_i`
containing `f_a(y)`. -/
def germAt {j : J} (a : j ⟶ i) {V : Opens (D.F.obj i)} (t : 𝒢.presheaf.obj (op V))
    (y : D.F.obj j) (hy : D.mapFun a y ∈ V) : GermPullback.Germs 𝒢.presheaf :=
  ⟨D.mapFun a y, 𝒢.presheaf.germ V (D.mapFun a y) hy t⟩

/-- The germ of a fixed section depends only on the point of the stage. -/
lemma germAt_congr {j : J} (a : j ⟶ i) {V : Opens (D.F.obj i)} (t : 𝒢.presheaf.obj (op V))
    {y y' : D.F.obj j} (hy : D.mapFun a y ∈ V) (hy' : D.mapFun a y' ∈ V) (e : y = y') :
    D.germAt 𝒢 a t y hy = D.germAt 𝒢 a t y' hy' := by
  subst e; rfl

/-- Germs at a stage below `j` are the germs at `j` of the image point. -/
lemma germAt_comp {m j : J} (c : m ⟶ j) (a : j ⟶ i) {V : Opens (D.F.obj i)}
    (t : 𝒢.presheaf.obj (op V)) (z : D.F.obj m) (hz : D.mapFun (c ≫ a) z ∈ V)
    (hz' : D.mapFun a (D.mapFun c z) ∈ V) :
    D.germAt 𝒢 (c ≫ a) t z hz = D.germAt 𝒢 a t (D.mapFun c z) hz' :=
  GermPullback.Germs.mk_eq_mk t (D.mapFun_comp c a z) hz hz'

/-- Germs at a coordinate of a point of the limit are germs at the point itself. -/
lemma germAt_projFun {j : J} (a : j ⟶ i) {V : Opens (D.F.obj i)} (t : 𝒢.presheaf.obj (op V))
    (x : D.invLimit) (hx : D.mapFun a (D.projFun j x) ∈ V) (hx' : D.projFun i x ∈ V) :
    D.germAt 𝒢 a t (D.projFun j x) hx =
      ⟨D.projFun i x, 𝒢.presheaf.germ V (D.projFun i x) hx' t⟩ :=
  GermPullback.Germs.mk_eq_mk t (D.projFun_eq_mapFun a x).symm hx hx'

/-- Two sections of `𝒢` on opens of `X_i` whose germs agree at every point of `X` lying over a
quasi-compact open `W ⊆ X_j` have germs agreeing at every point over `W` at some stage
`c : m ⟶ j`. -/
private lemma exists_mapFun_germAt_eq {j : J} (a : j ⟶ i) (W : Opens (D.F.obj j))
    (hW : IsCompact (W : Set (D.F.obj j))) {V V' : Opens (D.F.obj i)}
    (t : 𝒢.presheaf.obj (op V)) (t' : 𝒢.presheaf.obj (op V'))
    (hV : ∀ z ∈ W, D.mapFun a z ∈ V) (hV' : ∀ z ∈ W, D.mapFun a z ∈ V')
    (h : ∀ (x : D.invLimit) (hx : D.projFun j x ∈ W),
      D.germAt 𝒢 a t (D.projFun j x) (hV _ hx) = D.germAt 𝒢 a t' (D.projFun j x) (hV' _ hx)) :
    ∃ (m : J) (c : m ⟶ j), ∀ (z : D.F.obj m) (hz : D.mapFun c z ∈ W),
      D.germAt 𝒢 a t (D.mapFun c z) (hV _ hz) = D.germAt 𝒢 a t' (D.mapFun c z) (hV' _ hz) :=
  D.exists_mapFun_eq_of_projFun_eq 𝒢 a W hW
    (GermPullback.ofSection (g := D.mapFun a) (fun z : W ↦ hV z.1 z.2) t)
    (GermPullback.ofSection (g := D.mapFun a) (fun z : W ↦ hV' z.1 z.2) t') h

/-- A finite family of sections of `𝒢` on opens of `X_i` whose germs agree over the limit `X` on
the overlaps of quasi-compact opens `W_l ⊆ X_j` has germs agreeing on those overlaps at a single
further stage `b : k ⟶ j`. -/
lemma exists_stage_germAt_pairwise_eq {j : J} (a : j ⟶ i) {ι : Type*} [Finite ι]
    (W : ι → Opens (D.F.obj j)) (hWc : ∀ l, IsCompact (W l : Set (D.F.obj j)))
    {V : ι → Opens (D.F.obj i)} (t : ∀ l, 𝒢.presheaf.obj (op (V l)))
    (hWV : ∀ (l : ι), ∀ z ∈ W l, D.mapFun a z ∈ V l)
    (h : ∀ (l l' : ι) (x : D.invLimit) (_ : D.projFun j x ∈ W l) (_ : D.projFun j x ∈ W l')
      (hV : D.mapFun a (D.projFun j x) ∈ V l) (hV' : D.mapFun a (D.projFun j x) ∈ V l'),
      D.germAt 𝒢 a (t l) (D.projFun j x) hV = D.germAt 𝒢 a (t l') (D.projFun j x) hV') :
    ∃ (k : J) (b : k ⟶ j), ∀ (l l' : ι) (z : D.F.obj k) (_ : D.mapFun b z ∈ W l)
      (_ : D.mapFun b z ∈ W l') (hV : D.mapFun (b ≫ a) z ∈ V l)
      (hV' : D.mapFun (b ≫ a) z ∈ V l'),
      D.germAt 𝒢 (b ≫ a) (t l) z hV = D.germAt 𝒢 (b ≫ a) (t l') z hV' := by
  classical
  have hpair : ∀ l l' : ι, ∃ (m : J) (c : m ⟶ j), ∀ (z : D.F.obj m)
      (_ : D.mapFun c z ∈ W l) (_ : D.mapFun c z ∈ W l')
      (hV : D.mapFun a (D.mapFun c z) ∈ V l) (hV' : D.mapFun a (D.mapFun c z) ∈ V l'),
      D.germAt 𝒢 a (t l) (D.mapFun c z) hV = D.germAt 𝒢 a (t l') (D.mapFun c z) hV' := by
    intro l l'
    have hint : IsCompact ((W l ⊓ W l' : Opens (D.F.obj j)) : Set (D.F.obj j)) := by
      rw [Opens.coe_inf]
      exact (hWc l).inter_of_isOpen (hWc l') (W l).isOpen (W l').isOpen
    obtain ⟨m, c, hc⟩ := D.exists_mapFun_germAt_eq 𝒢 a (W l ⊓ W l') hint (t l) (t l')
      (fun z hz ↦ hWV l z hz.1) (fun z hz ↦ hWV l' z hz.2)
      fun x hx ↦ h l l' x hx.1 hx.2 _ _
    exact ⟨m, c, fun z hz hz' _ _ ↦ hc z ⟨hz, hz'⟩⟩
  choose mp cp hcp using hpair
  obtain ⟨k, b, -, hfac⟩ := exists_common_factoring (fun p : ι × ι ↦ mp p.1 p.2)
    (fun p ↦ cp p.1 p.2) (𝟙 j)
  refine ⟨k, b, fun l l' z hz hz' hV hV' ↦ ?_⟩
  obtain ⟨u, hu⟩ := hfac (l, l')
  have e := D.mapFun_mapFun_eq hu z
  have h₁ : D.mapFun (cp l l') (D.mapFun u z) ∈ W l := by rw [e]; exact hz
  have h₂ : D.mapFun (cp l l') (D.mapFun u z) ∈ W l' := by rw [e]; exact hz'
  calc D.germAt 𝒢 (b ≫ a) (t l) z hV
      = D.germAt 𝒢 a (t l) (D.mapFun b z) (hWV l _ hz) := D.germAt_comp 𝒢 b a (t l) z _ _
    _ = D.germAt 𝒢 a (t l) (D.mapFun (cp l l') (D.mapFun u z)) (hWV l _ h₁) :=
        D.germAt_congr 𝒢 a (t l) _ _ e.symm
    _ = D.germAt 𝒢 a (t l') (D.mapFun (cp l l') (D.mapFun u z)) (hWV l' _ h₂) :=
        hcp l l' (D.mapFun u z) h₁ h₂ _ _
    _ = D.germAt 𝒢 a (t l') (D.mapFun b z) (hWV l' _ hz') := D.germAt_congr 𝒢 a (t l') _ _ e
    _ = D.germAt 𝒢 (b ≫ a) (t l') z hV' := (D.germAt_comp 𝒢 b a (t l') z _ _).symm

/-! ### Surjectivity of the canonical map -/

/-- Around every point of `p_i⁻¹(U)` there are a quasi-compact open `W` of `X` inside `p_i⁻¹(U)`, a
quasi-compact open `V` of `X_i` containing `p_i(W)`, and a section `t` of `𝒢` over `V` whose germs
give the section on `W`. -/
lemma exists_compact_repr (s : D.limSections U 𝒢) {x : D.invLimit} (hx : x ∈ D.limPre U) :
    ∃ (W : Opens D.invLimit) (_ : x ∈ W) (_ : IsCompact (W : Set D.invLimit))
      (_ : W ≤ D.limPre U) (V : Opens (D.F.obj i)) (_ : IsCompact (V : Set (D.F.obj i)))
      (_ : ∀ z ∈ W, D.projFun i z ∈ V) (t : 𝒢.presheaf.obj (op V)),
      ∀ (z : D.invLimit), z ∈ W → ∀ (hz : z ∈ D.limPre U) (hzV : D.projFun i z ∈ V),
        s.1 ⟨z, hz⟩ = ⟨D.projFun i z, 𝒢.presheaf.germ V (D.projFun i z) hzV t⟩ := by
  have : SpectralSpace D.invLimit := spectralDiagram_invLimit_spectralSpace D
  obtain ⟨W₀, hxW₀, iW, V₀, hV₀, t₀, ht₀⟩ := GermPullback.exists_repr s hx
  obtain ⟨V', ⟨hV'o, hV'c⟩, hxV', hV'V₀⟩ :=
    (PrespectralSpace.isTopologicalBasis (X := D.F.obj i)).exists_subset_of_mem_open
      (hV₀ ⟨x, hxW₀⟩) V₀.isOpen
  have hVle : (⟨V', hV'o⟩ : Opens (D.F.obj i)) ≤ V₀ := hV'V₀
  obtain ⟨W', ⟨hW'o, hW'c⟩, hxW', hW'W₁⟩ :=
    (PrespectralSpace.isTopologicalBasis (X := D.invLimit)).exists_subset_of_mem_open
      (a := x) (u := (W₀ ⊓ (Opens.map (D.proj i)).obj ⟨V', hV'o⟩ : Opens D.invLimit))
      ⟨hxW₀, hxV'⟩ (W₀ ⊓ (Opens.map (D.proj i)).obj ⟨V', hV'o⟩).isOpen
  refine ⟨⟨W', hW'o⟩, hxW', hW'c, fun z hz ↦ iW.le (hW'W₁ hz).1, ⟨V', hV'o⟩, hV'c,
    fun z hz ↦ (hW'W₁ hz).2, 𝒢.presheaf.map (homOfLE hVle).op t₀, ?_⟩
  intro z hzW hz hzV
  show s.1 (iW ⟨z, (hW'W₁ hzW).1⟩) = _
  rw [ht₀ ⟨z, (hW'W₁ hzW).1⟩]
  exact congrArg (fun u ↦ (⟨D.projFun i z, u⟩ : GermPullback.Germs 𝒢.presheaf))
    (𝒢.presheaf.germ_res_apply (homOfLE hVle) (D.projFun i z) hzV t₀).symm

/-- A section of `p_i⁻¹𝒢` over `p_i⁻¹(U)` is germwise given, on each member of a finite covering of
`p_i⁻¹(U)` by quasi-compact opens `W_l`, by a section `t_l` of `𝒢` over a quasi-compact open
`V_l ⊆ X_i` containing `p_i(W_l)`. -/
lemma exists_finite_compact_repr (hU : IsCompact (U : Set (D.F.obj i))) (s : D.limSections U 𝒢) :
    ∃ (n : ℕ) (W : Fin n → Opens D.invLimit) (V : Fin n → Opens (D.F.obj i))
      (t : ∀ l, 𝒢.presheaf.obj (op (V l))),
      (∀ l, IsCompact (W l : Set D.invLimit)) ∧
      (∀ l, IsCompact (V l : Set (D.F.obj i))) ∧
      (∀ (l : Fin n), ∀ z ∈ W l, D.projFun i z ∈ V l) ∧
      ((D.limPre U : Set D.invLimit) = ⋃ l, (W l : Set D.invLimit)) ∧
      (∀ (l : Fin n) (z : D.invLimit), z ∈ W l → ∀ (hz : z ∈ D.limPre U)
        (hzV : D.projFun i z ∈ V l),
        s.1 ⟨z, hz⟩ = ⟨D.projFun i z, 𝒢.presheaf.germ (V l) (D.projFun i z) hzV (t l)⟩) := by
  classical
  choose Wf hxWf hWfc hWfle Vf hVfc hVf tf htf using
    fun p : D.limPre U ↦ D.exists_compact_repr U 𝒢 s p.2
  have hcpt : IsCompact (D.limPre U : Set D.invLimit) :=
    (spectralDiagram_proj_isSpectralMap D i).isCompact_preimage_of_isOpen U.isOpen hU
  obtain ⟨fs, hfs⟩ := hcpt.elim_finite_subcover (fun p : D.limPre U ↦ (Wf p : Set D.invLimit))
    (fun p ↦ (Wf p).isOpen) fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxWf ⟨x, hx⟩⟩
  refine ⟨fs.card, fun l ↦ Wf (fs.equivFin.symm l).1, fun l ↦ Vf (fs.equivFin.symm l).1,
    fun l ↦ tf (fs.equivFin.symm l).1, fun l ↦ hWfc _, fun l ↦ hVfc _, fun l ↦ hVf _, ?_,
    fun l ↦ htf _⟩
  refine Set.Subset.antisymm (fun x hx ↦ ?_) (Set.iUnion_subset fun l ↦ hWfle _)
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hfs hx)
  refine Set.mem_iUnion.mpr ⟨fs.equivFin ⟨p, hp⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hxp

/-- Finitely many quasi-compact opens of the limit `X` are the preimages of quasi-compact opens at
a single stage, which may be taken over any prescribed object `A` of the index category. -/
lemma exists_stage_preimage {ι : Type*} [Finite ι] (W : ι → Set D.invLimit)
    (hWo : ∀ l, IsOpen (W l)) (hWc : ∀ l, IsCompact (W l)) (A : J) :
    ∃ (j₀ : J) (_ : j₀ ⟶ A) (W₀ : ι → Set (D.F.obj j₀)),
      (∀ l, IsOpen (W₀ l)) ∧ (∀ l, IsCompact (W₀ l)) ∧
      ∀ l, D.projFun j₀ ⁻¹' W₀ l = W l := by
  classical
  choose jl Sl hSlo hSlc hSl using fun l ↦
    SpectralLimits.descent_of_quasiCompact_opens D.F D.isSpectralDiagram.2 (W l) (hWo l) (hWc l)
  obtain ⟨j₀, ⟨a₀⟩, hcl⟩ := exists_common_lowerBound jl A
  refine ⟨j₀, a₀, fun l ↦ D.mapFun (hcl l).some ⁻¹' Sl l,
    fun l ↦ (hSlo l).preimage (D.mapFun_continuous _),
    fun l ↦ (D.isSpectralMap_mapFun _).isCompact_preimage_of_isOpen (hSlo l) (hSlc l),
    fun l ↦ ?_⟩
  rw [D.preimage_projFun_preimage_mapFun]
  exact hSl l

/-- An inclusion between a quasi-compact open of a stage `j₀` and the pullback along `a : j₀ ⟶ i`
of a quasi-compact open of `X_i`, holding after pulling both back to the limit `X`, already holds
after a single further morphism `γ : m ⟶ j₀`. -/
lemma exists_stage_inclusion {j₀ : J} (a : j₀ ⟶ i) {W : Set (D.F.obj j₀)}
    (hWo : IsOpen W) (hWc : IsCompact W) {V : Set (D.F.obj i)}
    (hVo : IsOpen V) (hVc : IsCompact V)
    (hsub : D.projFun j₀ ⁻¹' W ⊆ D.projFun i ⁻¹' V) :
    ∃ (m : J) (γ : m ⟶ j₀), D.mapFun γ ⁻¹' W ⊆ D.mapFun γ ⁻¹' (D.mapFun a ⁻¹' V) := by
  have hVo' : IsOpen (D.mapFun a ⁻¹' V) := hVo.preimage (D.mapFun_continuous a)
  have hVc' : IsCompact (D.mapFun a ⁻¹' V) :=
    (D.isSpectralMap_mapFun a).isCompact_preimage_of_isOpen hVo hVc
  have hsub' : D.projFun j₀ ⁻¹' W ⊆ D.projFun j₀ ⁻¹' (D.mapFun a ⁻¹' V) := by
    rw [D.preimage_projFun_preimage_mapFun]
    exact hsub
  obtain ⟨k, α, β, hαβ⟩ := SpectralLimits.descent_of_inclusions D.F D.isSpectralDiagram.2 j₀ j₀ W
    (D.mapFun a ⁻¹' V) hWo hWc hVo' hVc' hsub'
  have hαβ' : D.mapFun α ⁻¹' W ⊆ D.mapFun β ⁻¹' (D.mapFun a ⁻¹' V) := hαβ
  refine ⟨IsCofiltered.eq α β, IsCofiltered.eqHom α β ≫ α, fun z hz ↦ ?_⟩
  have hz0 : D.mapFun (IsCofiltered.eqHom α β ≫ α) z ∈ W := hz
  rw [D.mapFun_comp] at hz0
  rw [Set.mem_preimage, Set.mem_preimage, IsCofiltered.eq_condition α β, D.mapFun_comp]
  exact hαβ' hz0

/-- If `f_γ⁻¹(W) ⊆ f_γ⁻¹(f_a⁻¹(V))` and `d` factors through `γ`, then
`f_d⁻¹(W) ⊆ f_{d ≫ a}⁻¹(V)`. -/
lemma mapFun_preimage_subset_of_factors {j₀ m j : J} {γ : m ⟶ j₀} (a : j₀ ⟶ i)
    {W : Set (D.F.obj j₀)} {V : Set (D.F.obj i)}
    (hγ : D.mapFun γ ⁻¹' W ⊆ D.mapFun γ ⁻¹' (D.mapFun a ⁻¹' V))
    {d : j ⟶ j₀} {u : j ⟶ m} (hu : u ≫ γ = d) :
    D.mapFun d ⁻¹' W ⊆ D.mapFun (d ≫ a) ⁻¹' V := by
  intro z hz
  have e := D.mapFun_mapFun_eq hu z
  have hz1 : D.mapFun γ (D.mapFun u z) ∈ W := by rw [e]; exact hz
  have hz2 : D.mapFun a (D.mapFun γ (D.mapFun u z)) ∈ V := hγ hz1
  rw [e] at hz2
  rw [Set.mem_preimage, D.mapFun_comp]
  exact hz2

/-- If `f_{a₁}⁻¹(f_a⁻¹(S)) = ⋃_l f_{a₁}⁻¹(W_l)` and `d` factors through `a₁`, then
`f_{d ≫ a}⁻¹(S) = ⋃_l f_d⁻¹(W_l)`. -/
lemma mapFun_preimage_eq_iUnion_of_factors {j₀ j₁ j : J} (a : j₀ ⟶ i) {a₁ : j₁ ⟶ j₀}
    {ι : Type*} {W : ι → Set (D.F.obj j₀)} {S : Set (D.F.obj i)}
    (hun : D.mapFun a₁ ⁻¹' (D.mapFun a ⁻¹' S) = ⋃ l, D.mapFun a₁ ⁻¹' W l)
    {d : j ⟶ j₀} {u : j ⟶ j₁} (hu : u ≫ a₁ = d) :
    D.mapFun (d ≫ a) ⁻¹' S = ⋃ l, D.mapFun d ⁻¹' W l := by
  have hd := D.mapFun_mapFun_eq hu
  refine Set.ext fun z ↦ ?_
  have h : (D.mapFun u z ∈ D.mapFun a₁ ⁻¹' (D.mapFun a ⁻¹' S)) ↔
      (D.mapFun u z ∈ ⋃ l, D.mapFun a₁ ⁻¹' W l) := by rw [hun]
  simpa only [Set.mem_iUnion, Set.mem_preimage, hd z, D.mapFun_comp] using h

/-- Given a quasi-compact open `U ⊆ X_i`, a finite covering of `p_i⁻¹(U)` by quasi-compact opens
`W_l` of `X`, and quasi-compact opens `V_l ⊆ X_i` with `p_i(W_l) ⊆ V_l`, there are a stage
`a : j ⟶ i` and quasi-compact opens `W_{l,j}` of `X_j` whose preimages in `X` are the `W_l`, which
cover `f_a⁻¹(U)`, and which satisfy `W_{l,j} ⊆ f_a⁻¹(V_l)`. -/
lemma exists_stage_covering (hU : IsCompact (U : Set (D.F.obj i))) {n : ℕ}
    (W : Fin n → Opens D.invLimit) (hWc : ∀ l, IsCompact (W l : Set D.invLimit))
    (V : Fin n → Opens (D.F.obj i)) (hVc : ∀ l, IsCompact (V l : Set (D.F.obj i)))
    (hWV : ∀ (l : Fin n), ∀ z ∈ W l, D.projFun i z ∈ V l)
    (hcov : (D.limPre U : Set D.invLimit) = ⋃ l, (W l : Set D.invLimit)) :
    ∃ (j : J) (a : j ⟶ i) (Wj : Fin n → Opens (D.F.obj j)),
      (∀ l, IsCompact (Wj l : Set (D.F.obj j))) ∧
      (∀ l, (W l : Set D.invLimit) = D.projFun j ⁻¹' (Wj l)) ∧
      (D.mapFun a ⁻¹' (U : Set (D.F.obj i)) = ⋃ l, (Wj l : Set (D.F.obj j))) ∧
      (∀ (l : Fin n), ∀ z ∈ Wj l, D.mapFun a z ∈ V l) := by
  classical
  obtain ⟨j₀, a₀, W₀, hW₀o, hW₀c, hW₀pre⟩ :=
    D.exists_stage_preimage (fun l ↦ (W l : Set D.invLimit)) (fun l ↦ (W l).isOpen) hWc i
  have hU₀o : IsOpen (D.mapFun a₀ ⁻¹' (U : Set (D.F.obj i))) :=
    U.isOpen.preimage (D.mapFun_continuous a₀)
  have hU₀c : IsCompact (D.mapFun a₀ ⁻¹' (U : Set (D.F.obj i))) :=
    (D.isSpectralMap_mapFun a₀).isCompact_preimage_of_isOpen U.isOpen hU
  have hU₀pre : D.projFun j₀ ⁻¹' (D.mapFun a₀ ⁻¹' (U : Set (D.F.obj i))) =
      (D.limPre U : Set D.invLimit) := by
    exact D.preimage_projFun_preimage_mapFun a₀ _
  have hunion0 : D.projFun j₀ ⁻¹' (D.mapFun a₀ ⁻¹' (U : Set (D.F.obj i))) =
      ⋃ l, D.projFun j₀ ⁻¹' W₀ l := by
    simp only [hW₀pre]
    rw [hU₀pre, hcov]
  obtain ⟨j₁, a₁, hun1⟩ := SpectralLimits.descent_of_finite_unions D.F D.isSpectralDiagram.2 j₀ n
    (D.mapFun a₀ ⁻¹' (U : Set (D.F.obj i))) W₀ hU₀o hU₀c (fun l ↦ ⟨hW₀o l, hW₀c l⟩) hunion0
  have hun1' : D.mapFun a₁ ⁻¹' (D.mapFun a₀ ⁻¹' (U : Set (D.F.obj i))) =
      ⋃ l, D.mapFun a₁ ⁻¹' W₀ l := hun1
  have hsub : ∀ l, D.projFun j₀ ⁻¹' W₀ l ⊆ D.projFun i ⁻¹' (V l : Set (D.F.obj i)) := by
    intro l x hx
    rw [hW₀pre l] at hx
    exact hWV l x hx
  choose ml γl hγl using fun l ↦
    D.exists_stage_inclusion a₀ (hW₀o l) (hW₀c l) (V l).isOpen (hVc l) (hsub l)
  obtain ⟨j, d, ⟨u₁, hu₁⟩, hfac⟩ := exists_common_factoring ml γl a₁
  refine ⟨j, d ≫ a₀, fun l ↦ ⟨D.mapFun d ⁻¹' W₀ l, (hW₀o l).preimage (D.mapFun_continuous d)⟩,
    fun l ↦ (D.isSpectralMap_mapFun d).isCompact_preimage_of_isOpen (hW₀o l) (hW₀c l), ?_, ?_, ?_⟩
  · intro l
    rw [← hW₀pre l]
    exact (D.preimage_projFun_preimage_mapFun d _).symm
  · exact D.mapFun_preimage_eq_iUnion_of_factors a₀ hun1' hu₁
  · intro l z hz
    obtain ⟨u, hu⟩ := hfac l
    exact D.mapFun_preimage_subset_of_factors a₀ (hγl l) hu hz

/-- Germwise sections at a stage `b ≫ a`, agreeing on the overlaps of the covering of `f_a⁻¹(U)`
obtained by pulling the `W_l` back along `b`, glue to a single section of `f_{b ≫ a}⁻¹𝒢` over
`f_{b ≫ a}⁻¹(U)` whose value at each point is the germ of the corresponding `t_l`. -/
lemma exists_section_of_germAt_pairwise_eq {j k : J} (a : j ⟶ i) (b : k ⟶ j) {ι : Type*}
    (W : ι → Opens (D.F.obj j))
    (hWU : D.mapFun a ⁻¹' (U : Set (D.F.obj i)) = ⋃ l, (W l : Set (D.F.obj j)))
    {V : ι → Opens (D.F.obj i)} (t : ∀ l, 𝒢.presheaf.obj (op (V l)))
    (hWV : ∀ (l : ι), ∀ z ∈ W l, D.mapFun a z ∈ V l)
    (hagree : ∀ (l l' : ι) (z : D.F.obj k) (_ : D.mapFun b z ∈ W l) (_ : D.mapFun b z ∈ W l')
      (hV : D.mapFun (b ≫ a) z ∈ V l) (hV' : D.mapFun (b ≫ a) z ∈ V l'),
      D.germAt 𝒢 (b ≫ a) (t l) z hV = D.germAt 𝒢 (b ≫ a) (t l') z hV') :
    ∃ ρ : (D.sliceFunctor U 𝒢).obj (op (Over.mk (b ≫ a))),
      ∀ (l : ι) (z : D.F.obj k) (_ : D.mapFun b z ∈ W l)
        (hzU : z ∈ D.slicePre U (Over.mk (b ≫ a))) (hV : D.mapFun (b ≫ a) z ∈ V l),
        ρ.1 ⟨z, hzU⟩ = D.germAt 𝒢 (b ≫ a) (t l) z hV := by
  have hV : ∀ (l : ι) (z : D.F.obj k), D.mapFun b z ∈ W l → D.mapFun (b ≫ a) z ∈ V l :=
    fun l z hz ↦ by
      rw [D.mapFun_comp]
      exact hWV l _ hz
  have hid : ∀ T : Set (D.F.obj j), D.mapFun (𝟙 j) ⁻¹' T = T :=
    fun T ↦ Set.ext fun z ↦ by rw [Set.mem_preimage, D.mapFun_id]
  have hkey : D.mapFun (b ≫ a) ⁻¹' (U : Set (D.F.obj i)) =
      ⋃ l, D.mapFun b ⁻¹' (W l : Set (D.F.obj j)) :=
    D.mapFun_preimage_eq_iUnion_of_factors (a₁ := 𝟙 j) a
      (W := fun l ↦ (W l : Set (D.F.obj j))) (by simp only [hid]; exact hWU) (Category.comp_id b)
  have hle : ∀ l, (Opens.map (D.F.map b)).obj (W l) ≤ D.slicePre U (Over.mk (b ≫ a)) :=
    fun l _ hz ↦ hkey.ge (Set.mem_iUnion.mpr ⟨l, hz⟩)
  have hcovk : ∀ z ∈ D.slicePre U (Over.mk (b ≫ a)),
      ∃ l, z ∈ (Opens.map (D.F.map b)).obj (W l) := fun _ hz ↦ Set.mem_iUnion.mp (hkey.le hz)
  obtain ⟨ρ, hρ⟩ := GermPullback.exists_glue (g := D.mapFun (b ≫ a)) (𝒢 := 𝒢.presheaf)
    (W := D.slicePre U (Over.mk (b ≫ a))) _ hle hcovk
    (fun l ↦ GermPullback.ofSection (g := D.mapFun (b ≫ a)) (fun z ↦ hV l z.1 z.2) (t l))
    fun l l' z hz hz' ↦ hagree l l' z hz hz' (hV l z hz) (hV l' z hz')
  exact ⟨ρ, fun l z hz _ _ ↦ hρ l z hz⟩

/-- Two germwise descriptions of one section of `p_i⁻¹𝒢` over `p_i⁻¹(U)` agree: a section `ρ` at a
stage `b ≫ a` given near each point by the germ of `t_l`, and a section `s` of `p_i⁻¹𝒢` given at
each point of `p_j⁻¹(W_l)` by the germ of the same `t_l`, have the same pullback to the limit. -/
lemma toLim_eq_of_germAt_eq {j k : J} (a : j ⟶ i) (b : k ⟶ j) {ι : Type*}
    (W : ι → Opens (D.F.obj j))
    (hWU : D.mapFun a ⁻¹' (U : Set (D.F.obj i)) = ⋃ l, (W l : Set (D.F.obj j)))
    {V : ι → Opens (D.F.obj i)} (t : ∀ l, 𝒢.presheaf.obj (op (V l)))
    (hWV : ∀ (l : ι), ∀ z ∈ W l, D.mapFun a z ∈ V l)
    (ρ : (D.sliceFunctor U 𝒢).obj (op (Over.mk (b ≫ a))))
    (hρ : ∀ (l : ι) (z : D.F.obj k) (_ : D.mapFun b z ∈ W l)
      (hzU : z ∈ D.slicePre U (Over.mk (b ≫ a))) (hV : D.mapFun (b ≫ a) z ∈ V l),
      ρ.1 ⟨z, hzU⟩ = D.germAt 𝒢 (b ≫ a) (t l) z hV)
    (s : D.limSections U 𝒢)
    (hs : ∀ (l : ι) (x : D.limPre U) (_ : D.projFun j x.1 ∈ W l)
      (hV : D.mapFun a (D.projFun j x.1) ∈ V l),
      s.1 x = D.germAt 𝒢 a (t l) (D.projFun j x.1) hV) :
    D.toLim U 𝒢 (Over.mk (b ≫ a)) ρ = s := by
  refine GermPullback.ext fun x ↦ ?_
  obtain ⟨l, hxl⟩ : ∃ l, D.projFun j x.1 ∈ (W l : Set (D.F.obj j)) := by
    refine Set.mem_iUnion.mp (hWU.le ?_)
    rw [Set.mem_preimage, ← D.projFun_eq_mapFun a x.1]
    exact x.2
  have hzW : D.mapFun b (D.projFun k x.1) ∈ W l := by
    rw [← D.projFun_eq_mapFun b x.1]
    exact hxl
  have hVk : D.mapFun (b ≫ a) (D.projFun k x.1) ∈ V l := by
    rw [D.mapFun_comp]
    exact hWV l _ hzW
  calc (D.toLim U 𝒢 (Over.mk (b ≫ a)) ρ).1 x
      = ρ.1 ⟨D.projFun k x.1, D.proj_mem U x⟩ := D.toLim_val U 𝒢 (Over.mk (b ≫ a)) ρ x
    _ = D.germAt 𝒢 (b ≫ a) (t l) (D.projFun k x.1) hVk := hρ l _ hzW _ hVk
    _ = D.germAt 𝒢 a (t l) (D.mapFun b (D.projFun k x.1)) (hWV l _ hzW) :=
        D.germAt_comp 𝒢 b a (t l) _ hVk (hWV l _ hzW)
    _ = D.germAt 𝒢 a (t l) (D.projFun j x.1) (hWV l _ hxl) :=
        D.germAt_congr 𝒢 a (t l) _ _ (D.projFun_eq_mapFun b x.1).symm
    _ = s.1 x := (hs l x hxl (hWV l _ hxl)).symm

/-- The canonical map is surjective when `U` is quasi-compact. -/
theorem surjective_canonicalMap [UnivLE.{max v v', max v u}]
    (hU : IsCompact (U : Set (D.F.obj i))) :
    Function.Surjective (D.canonicalMap U 𝒢) := by
  intro s
  obtain ⟨n, W, V, t, hWc, hVc, hWV, hcov, hst⟩ := D.exists_finite_compact_repr U 𝒢 hU s
  obtain ⟨j, a, Wj, hWjc, hWjpre, hWjU, hWjV⟩ :=
    D.exists_stage_covering U hU W hWc V hVc hWV hcov
  have hs : ∀ (l : Fin n) (x : D.limPre U) (_ : D.projFun j x.1 ∈ Wj l)
      (hV : D.mapFun a (D.projFun j x.1) ∈ V l),
      s.1 x = D.germAt 𝒢 a (t l) (D.projFun j x.1) hV := by
    intro l x hx hV
    have hxl : x.1 ∈ (W l : Set D.invLimit) := by rw [hWjpre l]; exact hx
    exact (hst l x.1 hxl x.2 (hWV l x.1 hxl)).trans
      (D.germAt_projFun 𝒢 a (t l) x.1 hV (hWV l x.1 hxl)).symm
  have hmem : ∀ (l : Fin n) (x : D.invLimit), D.projFun j x ∈ Wj l → x ∈ D.limPre U := by
    intro l x hx
    rw [mem_limPre, D.projFun_eq_mapFun a x]
    exact hWjU.ge (Set.mem_iUnion.mpr ⟨l, hx⟩)
  obtain ⟨k, b, hagree⟩ := D.exists_stage_germAt_pairwise_eq 𝒢 a Wj hWjc t hWjV
    fun l l' x hx hx' hV hV' ↦
      (hs l ⟨x, hmem l x hx⟩ hx hV).symm.trans (hs l' ⟨x, hmem l x hx⟩ hx' hV')
  obtain ⟨ρ, hρ⟩ := D.exists_section_of_germAt_pairwise_eq U 𝒢 a b Wj hWjU t hWjV hagree
  exact ⟨colimit.ι (D.sliceFunctor U 𝒢) (op (Over.mk (b ≫ a))) ρ,
    (D.canonicalMap_ι_apply U 𝒢 (Over.mk (b ≫ a)) ρ).trans
      (D.toLim_eq_of_germAt_eq U 𝒢 a b Wj hWjU t hWjV ρ hρ s hs)⟩

/-- For `i` an object of the cofiltered index category, `𝒢` a sheaf of sets on `X_i` and `U ⊆ X_i`
a quasi-compact open, the canonical map `colim_{a : j → i} (f_a⁻¹𝒢)(f_a⁻¹ U) → (p_i⁻¹𝒢)(p_i⁻¹ U)`
is bijective. -/
@[stacks 0A32 "bijectivity of the canonical map"]
theorem bijective_canonicalMap [UnivLE.{max v v', max v u}] (hU : IsCompact (U : Set (D.F.obj i))) :
    Function.Bijective (D.canonicalMap U 𝒢) :=
  ⟨D.injective_canonicalMap U 𝒢 hU, D.surjective_canonicalMap U 𝒢 hU⟩

end SpectralDiagram
