module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.Topology.Simplicial.DiagramSite

/-!
# The slice of the total site of a diagram of spaces

Let `X` be a diagram of topological spaces indexed by a category `A`, and let `(n, W)` be an
object of its total site: an index `n` together with an open `W` of the space `X_n`. An object of
the slice of the total site at `(n, W)` is an object `(m, V)` of the total site together with an
arrow into `(n, W)`, that is: an arrow `φ : m ⟶ n` of `A` and an open `V` of `X_m` contained in
the inverse image `(X φ)⁻¹W`.

The slice is therefore *not* the site of opens of `W`. It is the total site of a new diagram of
spaces, indexed by the slice category `A/n`, whose space at `φ : m ⟶ n` is the open subspace
`(X φ)⁻¹W` of `X_m`. This file constructs that diagram and identifies the two sites, as an
equivalence of sites in the sense of `CategoryTheory.Functor.IsDenseSubsite`, hence an
equivalence of their categories of sheaves.

## Main definitions

* `Stacks.Topology.Simplicial.overSpace`: the diagram of spaces over an object of the total
  site.
* `Stacks.Topology.Simplicial.DiagramOpen.sliceFunctor` and `.sliceInverse`: the two comparison
  functors between the slice of the total site and the total site of the over-diagram.
* `Stacks.Topology.Simplicial.DiagramOpen.sliceEquivalence`: they form an equivalence of
  categories; `sliceFunctor_obj_index` and `sliceFunctor_obj_toOpens` read off what it does to
  an object.
* `Stacks.Topology.Simplicial.DiagramOpen.sheafSliceEquivalence`: the induced equivalence of
  sheaf categories.

## Main results

* `Stacks.Topology.Simplicial.DiagramOpen.sliceFunctor_isDenseSubsite`: the comparison is an
  equivalence of *sites*: the slice topology on the slice of the total site corresponds to the
  topology of levelwise open coverings on the total site of the over-diagram.

## Implementation notes

The comparison is an equivalence of categories, not an isomorphism: on opens it is the passage
between an open of the subspace `(X φ)⁻¹W` and an open of `X_m` contained in `(X φ)⁻¹W`, which is
a bijection but not an equality. On indices it is the passage between an arrow `φ : m ⟶ n` of `A`
and the object `Over.mk φ` of `A/n`, which *is* an equality, by eta for structures; that is what
makes the unit and counit levelwise, i.e. identities on indices.

Both topologies are described pointwise by
`Stacks.Topology.Simplicial.DiagramOpen.mem_grothendieckTopology_iff`, and that is how
`functorPushforward_mem_iff` is proved: a point of `W` over which the sieve is covering on one
side gives one on the other, the two opens corresponding under the bijection above. The
bookkeeping that remains is that the object `Over.mk (𝟙 ≫ φ)` of `A/n` produced by composing a
levelwise arrow with the structure arrow is only *isomorphic* to `Over.mk φ`, not equal to it,
since `𝟙 ≫ φ = φ` is not a definitional equality in a general category; the comparison arrow is
levelwise and is supplied explicitly on both sides.

The points of the space of the over-diagram at `φ` are handled through `overPt` and `overMk`
rather than through `Subtype.val` and the anonymous constructor: the object
`(overSpace X U).obj φ` of `TopCat` is produced by a definition, so the elaborator does not see
a subtype there, and projection notation and anonymous constructors fail against it. The two
abbreviations state the same maps at a type the elaborator does see.

The three `IsDenseSubsite` instances are the ones of Mathlib's
`TopologicalSpace.Opens.overEquivalence`, which identifies the slice of the site of opens of a
space with the site of opens of an open subspace: one instance is proved, and the other two are
the same statement for the inverse equivalence.

## References

* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 00XZ](https://stacks.math.columbia.edu/tag/00XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w v₁ u₁

namespace Stacks.Topology.Simplicial

variable {A : Type u₁} [Category.{v₁} A] {X : A ⥤ TopCat.{u}}

/-- The open of `X_m` whose subspace is the space of the over-diagram at an index `φ : m ⟶ n`
of the slice category. -/
abbrev overOpens (U : DiagramOpen X) (φ : Over U.index) : Opens (X.obj φ.left) :=
  (Opens.map (X.map φ.hom)).obj U.toOpens

/-- An arrow of the slice category carries the open `(X φ)⁻¹W` into the open `(X ψ)⁻¹W`. -/
theorem overSpace_mapsTo {U : DiagramOpen X} {φ ψ : Over U.index} (h : φ ⟶ ψ)
    (x : ↥(overOpens U φ)) : X.map h.left x.1 ∈ overOpens U ψ := by
  show X.map ψ.hom (X.map h.left x.1) ∈ U.toOpens
  rw [← Functor.map_comp_apply, Over.w h]
  exact x.2

/-- **The diagram of spaces over an object of the total site.** At an index `φ : m ⟶ n` of the
slice category `A/n` it is the open subspace `(X φ)⁻¹W` of `X_m`, and an arrow of the slice acts
by restricting the corresponding map of the diagram. -/
def overSpace (X : A ⥤ TopCat.{u}) (U : DiagramOpen X) : Over U.index ⥤ TopCat.{u} where
  obj φ := TopCat.of ↥(overOpens U φ)
  map h := TopCat.ofHom
    ⟨fun x => ⟨X.map h.left x.1, overSpace_mapsTo h x⟩,
      Continuous.subtype_mk ((X.map h.left).hom.continuous.comp continuous_subtype_val)
        (overSpace_mapsTo h)⟩
  map_id φ := TopCat.hom_ext (ContinuousMap.ext fun x =>
    Subtype.ext (ConcreteCategory.congr_hom (X.map_id φ.left) x.1))
  map_comp h k := TopCat.hom_ext (ContinuousMap.ext fun x =>
    Subtype.ext (Functor.map_comp_apply X h.left k.left x.1))

/-- The underlying point of `X_m` of a point of the space of the over-diagram at `φ`. -/
abbrev overPt (U : DiagramOpen X) (φ : Over U.index) (x : (overSpace X U).obj φ) :
    X.obj φ.left :=
  (x : ↥(overOpens U φ)).1

/-- A point of `X_m` lying in `(X φ)⁻¹W`, as a point of the space of the over-diagram at `φ`. -/
abbrev overMk (U : DiagramOpen X) (φ : Over U.index) (y : X.obj φ.left)
    (h : y ∈ overOpens U φ) : (overSpace X U).obj φ :=
  (⟨y, h⟩ : ↥(overOpens U φ))

/-- The underlying point of a point of the space of the over-diagram at `φ` lies in `(X φ)⁻¹W`. -/
theorem overPt_mem (U : DiagramOpen X) (φ : Over U.index) (x : (overSpace X U).obj φ) :
    overPt U φ x ∈ overOpens U φ :=
  (x : ↥(overOpens U φ)).2

/-- Passing to the underlying point of `X_m` is injective. -/
theorem overPt_injective (U : DiagramOpen X) (φ : Over U.index) :
    Function.Injective (overPt U φ) :=
  fun _ _ h => Subtype.ext h

/-- The underlying point of the image of `x` under an arrow `h` of the slice is the image of the
underlying point of `x` under `X h`. -/
@[simp]
theorem overPt_map (U : DiagramOpen X) {φ ψ : Over U.index} (h : φ ⟶ ψ)
    (x : (overSpace X U).obj φ) :
    overPt U ψ ((overSpace X U).map h x) = X.map h.left (overPt U φ x) := rfl

namespace DiagramOpen

variable {U : DiagramOpen X}

/-- The open of `X_m` underlying an open of the space of the over-diagram at `φ`. -/
def sliceImage (φ : Over U.index) (P : Opens ((overSpace X U).obj φ)) :
    Opens (X.obj φ.left) :=
  ⟨overPt U φ '' P.1,
    ((overOpens U φ).isOpenEmbedding'.isOpen_iff_image_isOpen).1 P.isOpen⟩

/-- The open of the space of the over-diagram at `φ` cut out by an open of `X_m`. -/
def slicePreimage (φ : Over U.index) (V : Opens (X.obj φ.left)) :
    Opens ((overSpace X U).obj φ) :=
  ⟨overPt U φ ⁻¹' V.1, V.isOpen.preimage continuous_subtype_val⟩

/-- A point lies in `slicePreimage φ V` if and only if its underlying point lies in `V`. -/
@[simp]
theorem mem_slicePreimage {φ : Over U.index} {V : Opens (X.obj φ.left)}
    {x : (overSpace X U).obj φ} : x ∈ slicePreimage φ V ↔ overPt U φ x ∈ V := Iff.rfl

/-- A point of `X_m` lies in `sliceImage φ P` if and only if it is the underlying point of a
point of `P`. -/
theorem mem_sliceImage_iff {φ : Over U.index} {P : Opens ((overSpace X U).obj φ)}
    {y : X.obj φ.left} : y ∈ sliceImage φ P ↔ ∃ x, x ∈ P ∧ overPt U φ x = y := Iff.rfl

/-- The underlying point of a point of `P` lies in `sliceImage φ P`. -/
theorem mem_sliceImage {φ : Over U.index} {P : Opens ((overSpace X U).obj φ)}
    {x : (overSpace X U).obj φ} (h : x ∈ P) : overPt U φ x ∈ sliceImage φ P :=
  ⟨x, h, rfl⟩

/-- Containment in a `slicePreimage` after transport along an arrow of the slice is the
pointwise statement about underlying points of `X_m`. -/
theorem le_map_slicePreimage_iff {φ ψ : Over U.index} (h : φ ⟶ ψ)
    (P : Opens ((overSpace X U).obj φ)) (V : Opens (X.obj ψ.left)) :
    P ≤ (Opens.map ((overSpace X U).map h)).obj (slicePreimage ψ V) ↔
      ∀ x ∈ P, X.map h.left (overPt U φ x) ∈ V :=
  ⟨fun hle _ hx => hle hx, fun hle _ hx => hle _ hx⟩

/-- Containment of a `sliceImage` in an inverse image is the pointwise statement about the
points of the open of the over-diagram. -/
theorem sliceImage_le_map_iff {φ : Over U.index} {T : TopCat.{u}} (b : X.obj φ.left ⟶ T)
    (P : Opens ((overSpace X U).obj φ)) (Q : Opens T) :
    sliceImage φ P ≤ (Opens.map b).obj Q ↔ ∀ x ∈ P, b (overPt U φ x) ∈ Q := by
  refine ⟨fun hle x hx => hle (mem_sliceImage hx), ?_⟩
  rintro hle y ⟨x, hx, rfl⟩
  exact hle x hx

/-- If `P` is contained in `slicePreimage φ V`, then `sliceImage φ P` is contained in `V`. -/
theorem sliceImage_le_of_le {φ : Over U.index} {P : Opens ((overSpace X U).obj φ)}
    {V : Opens (X.obj φ.left)} (h : P ≤ slicePreimage φ V) : sliceImage φ P ≤ V := by
  rintro y ⟨x, hx, rfl⟩
  exact h hx

/-- Cutting out by the underlying open of `P` recovers `P`. -/
theorem slicePreimage_sliceImage (φ : Over U.index) (P : Opens ((overSpace X U).obj φ)) :
    slicePreimage φ (sliceImage φ P) = P := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_sliceImage hx)
  obtain ⟨z, hz, hzx⟩ := hx
  exact overPt_injective U φ hzx ▸ hz

/-- For an open `V` of `X_m` contained in `(X φ)⁻¹W`, the open underlying the one cut out by `V`
is `V`. -/
theorem sliceImage_slicePreimage (φ : Over U.index) {V : Opens (X.obj φ.left)}
    (h : V ≤ overOpens U φ) : sliceImage φ (slicePreimage φ V) = V := by
  exact le_antisymm (sliceImage_le_of_le le_rfl) fun y hy => ⟨overMk U φ y (h hy), hy, rfl⟩

/-- **The slice of the total site, as the total site of the over-diagram.** An object of the
slice at `(n, W)` — an object `(m, V)` of the total site with an arrow into `(n, W)` — is sent to
the index `φ : m ⟶ n` of that arrow together with the open of `(X φ)⁻¹W` cut out by `V`. -/
def sliceFunctor (X : A ⥤ TopCat.{u}) (U : DiagramOpen X) :
    Over U ⥤ DiagramOpen (overSpace X U) where
  obj V := ⟨Over.mk V.hom.base, slicePreimage (Over.mk V.hom.base) V.left.toOpens⟩
  map f :=
    { base := Over.homMk f.left.base (congrArg Hom.base (Over.w f))
      le := (le_map_slicePreimage_iff _ _ _).2 fun _ hx => Hom.le f.left hx }
  map_id _ := Hom.ext _ _ (Over.OverMorphism.ext rfl)
  map_comp _ _ := Hom.ext _ _ (Over.OverMorphism.ext rfl)

/-- **The inverse of the slice comparison.** An object of the total site of the over-diagram —
an index `φ : m ⟶ n` and an open `P` of `(X φ)⁻¹W` — is sent to the open of `X_m` underlying
`P`, with the arrow into `(n, W)` lying over `φ`. -/
def sliceInverse (X : A ⥤ TopCat.{u}) (U : DiagramOpen X) :
    DiagramOpen (overSpace X U) ⥤ Over U where
  obj P := Over.mk (Y := ⟨P.index.left, sliceImage P.index P.toOpens⟩)
    { base := P.index.hom
      le := (sliceImage_le_map_iff _ _ _).2 fun x _ => overPt_mem U P.index x }
  map {P Q} h :=
    Over.homMk
      { base := h.base.left
        le := (sliceImage_le_map_iff _ _ _).2 fun x hx => by
          have hQ : (overSpace X U).map h.base x ∈ Q.toOpens := Hom.le h hx
          exact mem_sliceImage hQ }
      (Hom.ext _ _ (Over.w h.base))
  map_id _ := Over.OverMorphism.ext (Hom.ext _ _ rfl)
  map_comp _ _ := Over.OverMorphism.ext (Hom.ext _ _ rfl)

/-- The index that the slice comparison reads off an object of the slice is the arrow of `A`
underlying its structure arrow. -/
@[simp]
theorem sliceFunctor_obj_index {X : A ⥤ TopCat.{u}} {U : DiagramOpen X} (V : Over U) :
    ((sliceFunctor X U).obj V).index = Over.mk V.hom.base := rfl

/-- The open subset of `(X φ)⁻¹W` that the slice comparison reads off an object `(m, V)` of the
slice is the one cut out by `V`. -/
@[simp]
theorem sliceFunctor_obj_toOpens {X : A ⥤ TopCat.{u}} {U : DiagramOpen X} (V : Over U) :
    ((sliceFunctor X U).obj V).toOpens =
      slicePreimage (Over.mk V.hom.base) V.left.toOpens := rfl

/-- The arrow of `A` underlying the image of an arrow `f` under `sliceFunctor` is the arrow of `A`
underlying `f`. -/
@[simp]
theorem sliceFunctor_map_base_left {V V' : Over U} (f : V ⟶ V') :
    ((sliceFunctor X U).map f).base.left = f.left.base := rfl

/-- The arrow of `A` underlying the image of an arrow `h` under `sliceInverse` is the arrow of `A`
underlying `h`. -/
@[simp]
theorem sliceInverse_map_left_base {P Q : DiagramOpen (overSpace X U)} (h : P ⟶ Q) :
    ((sliceInverse X U).map h).left.base = h.base.left := rfl

/-- **The slice of the total site of a diagram of spaces is the total site of the
over-diagram.** -/
def sliceEquivalence (X : A ⥤ TopCat.{u}) (U : DiagramOpen X) :
    Over U ≌ DiagramOpen (overSpace X U) where
  functor := sliceFunctor X U
  inverse := sliceInverse X U
  unitIso := NatIso.ofComponents
    (fun V ↦ Over.isoMk
      (levelwiseIso (X := X) (a := V.left.index)
        (sliceImage_slicePreimage (U := U) (Over.mk V.hom.base) (Hom.le V.hom)).symm)
      (Hom.ext _ _ (Category.id_comp _)))
    (fun _ ↦ Over.OverMorphism.ext
      (Hom.ext _ _ ((Category.comp_id _).trans (Category.id_comp _).symm)))
  counitIso := NatIso.ofComponents
    (fun P ↦ levelwiseIso (X := overSpace X U) (a := P.index)
      (slicePreimage_sliceImage P.index P.toOpens))
    (fun _ ↦ Hom.ext _ _ (Over.OverMorphism.ext
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
  functor_unitIso_comp _ := Hom.ext _ _ (Over.OverMorphism.ext (Category.id_comp _))

variable (X U)

/-- A sieve on an object of the slice whose image under the slice comparison is a covering sieve
of the total site of the over-diagram is a covering sieve of the slice topology. -/
private theorem mem_over_of_functorPushforward_mem [IsoRigid A] {V : Over U} {S : Sieve V}
    (H : S.functorPushforward (sliceEquivalence X U).functor ∈
      grothendieckTopology (overSpace X U) ((sliceEquivalence X U).functor.obj V)) :
    S ∈ (grothendieckTopology X).over U V := by
  rw [mem_grothendieckTopology_iff] at H
  rw [GrothendieckTopology.mem_over_iff, mem_grothendieckTopology_iff]
  intro y hy
  obtain ⟨P, hP, hSP, hxP⟩ := H (overMk U (Over.mk V.hom.base) y (Hom.le V.hom hy)) hy
  obtain ⟨T, a, b, hSa, hcomp⟩ := hSP
  have hV₀ : sliceImage (Over.mk V.hom.base) P ≤ V.left.toOpens := sliceImage_le_of_le hP
  refine ⟨sliceImage (Over.mk V.hom.base) P, hV₀, ?_, mem_sliceImage hxP⟩
  rw [Sieve.overEquiv_iff]
  set k : Over.mk (levelHom V.left hV₀ ≫ V.hom) ⟶ V := Over.homMk (levelHom V.left hV₀)
    with hk
  set ι : Over.mk ((levelHom V.left hV₀ ≫ V.hom).base) ⟶ Over.mk V.hom.base :=
    Over.homMk (𝟙 V.left.index) rfl with hι
  have hρle : slicePreimage (Over.mk ((levelHom V.left hV₀ ≫ V.hom).base))
        (sliceImage (Over.mk V.hom.base) P) ≤ (Opens.map ((overSpace X U).map ι)).obj P := by
    rintro z ⟨x, hx, hxz⟩
    have key : (overSpace X U).map ι z = x := overPt_injective U (Over.mk V.hom.base)
      ((overPt_map U _ z).trans
        ((ConcreteCategory.congr_hom (X.map_id V.left.index) _).trans hxz.symm))
    change (overSpace X U).map ι z ∈ P
    exact key ▸ hx
  set ρ : (sliceEquivalence X U).functor.obj (Over.mk (levelHom V.left hV₀ ≫ V.hom)) ⟶
      ⟨Over.mk V.hom.base, P⟩ := { base := ι, le := hρle } with hρ
  have h1 : (sliceEquivalence X U).functor.map k =
      ρ ≫ ((sliceEquivalence X U).functor.obj V).levelHom hP := by
    rw [hk, hρ]
    exact Hom.ext _ _ (Over.OverMorphism.ext (Category.id_comp _).symm)
  have hmap : (sliceEquivalence X U).functor.map k = (ρ ≫ b) ≫
      (sliceEquivalence X U).functor.map a :=
    h1.trans ((congrArg (fun t => ρ ≫ t) hcomp).trans (Category.assoc _ _ _).symm)
  have hfac : k = (sliceEquivalence X U).functor.preimage (ρ ≫ b) ≫ a :=
    (sliceEquivalence X U).functor.map_injective
      (hmap.trans (by rw [Functor.map_comp, Functor.map_preimage]))
  rw [hfac]
  exact S.downward_closed hSa _

/-- The image under the slice comparison of a covering sieve of the slice topology is a covering
sieve of the total site of the over-diagram. -/
private theorem functorPushforward_mem_of_mem_over [IsoRigid A] {V : Over U} {S : Sieve V}
    (H : S ∈ (grothendieckTopology X).over U V) :
    S.functorPushforward (sliceEquivalence X U).functor ∈
      grothendieckTopology (overSpace X U) ((sliceEquivalence X U).functor.obj V) := by
  rw [GrothendieckTopology.mem_over_iff, mem_grothendieckTopology_iff] at H
  rw [mem_grothendieckTopology_iff]
  intro x hx
  obtain ⟨V₀, hV₀, hSV₀, hxV₀⟩ := H (overPt U (Over.mk V.hom.base) x) hx
  refine ⟨slicePreimage (Over.mk V.hom.base) V₀, fun _ hz => hV₀ hz, ?_, hxV₀⟩
  refine ⟨Over.mk (levelHom V.left hV₀ ≫ V.hom), Over.homMk (levelHom V.left hV₀), ?_,
    (Sieve.overEquiv_iff _ _).1 hSV₀, ?_⟩
  · have hw : 𝟙 V.left.index ≫ ((sliceEquivalence X U).functor.obj
          (Over.mk (levelHom V.left hV₀ ≫ V.hom))).index.hom =
        ((sliceEquivalence X U).functor.obj V).index.hom :=
      (Category.id_comp _).trans (Category.id_comp _)
    refine { base := Over.homMk (𝟙 V.left.index) hw, le := fun z hz => ?_ }
    show X.map (𝟙 V.left.index) (overPt U (Over.mk V.hom.base) z) ∈ V₀
    rw [ConcreteCategory.congr_hom (X.map_id V.left.index)]
    exact hz
  · exact Hom.ext _ _ (Over.OverMorphism.ext (Category.id_comp _).symm)

/-- **The slice comparison is an equivalence of sites.** The slice topology on the slice of the
total site at `(n, W)` corresponds to the topology of levelwise open coverings on the total site
of the over-diagram. -/
instance sliceFunctor_isDenseSubsite [IsoRigid A] :
    (sliceEquivalence X U).functor.IsDenseSubsite
      ((grothendieckTopology X).over U) (grothendieckTopology (overSpace X U)) where
  functorPushforward_mem_iff :=
    ⟨mem_over_of_functorPushforward_mem X U, functorPushforward_mem_of_mem_over X U⟩

/-- The inverse of the symmetric slice equivalence is an equivalence of sites from the slice of
the total site to the total site of the over-diagram. -/
instance [IsoRigid A] : (sliceEquivalence X U).symm.inverse.IsDenseSubsite
    ((grothendieckTopology X).over U) (grothendieckTopology (overSpace X U)) :=
  inferInstanceAs ((sliceEquivalence X U).functor.IsDenseSubsite ..)

/-- The inverse of the slice comparison is an equivalence of sites from the total site of the
over-diagram to the slice of the total site. -/
instance sliceInverse_isDenseSubsite [IsoRigid A] :
    (sliceEquivalence X U).inverse.IsDenseSubsite
      (grothendieckTopology (overSpace X U)) ((grothendieckTopology X).over U) :=
  inferInstanceAs ((sliceEquivalence X U).symm.functor.IsDenseSubsite ..)

/-- **Sheaves on the slice of the total site are sheaves on the total site of the
over-diagram.** -/
def sheafSliceEquivalence [IsoRigid A] (B : Type w) [Category.{v} B] :
    Sheaf ((grothendieckTopology X).over U) B ≌
      Sheaf (grothendieckTopology (overSpace X U)) B :=
  (sliceEquivalence X U).sheafCongr _ _ B

end DiagramOpen

end Stacks.Topology.Simplicial

end
