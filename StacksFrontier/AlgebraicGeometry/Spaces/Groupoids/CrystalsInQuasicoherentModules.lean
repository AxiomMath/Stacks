module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.GabberDirected
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward

/-!
# Crystals in quasi-coherent modules on a system of schemes

Fix a set `I`, a set `Φ` and a map `j : Φ → I × I`, a scheme `X i` for each `i ∈ I`, and for
each `φ ∈ Φ` with `j φ = (i, i')` a morphism of schemes `f φ : X i' ⟶ X i`.  A *crystal in
quasi-coherent modules* on `X = ({X i}, {f φ})` is a quasi-coherent module `F i` on each `X i`
together with an isomorphism `α φ : (f φ)^* (F i) ≅ F i'` for each `φ`; these form the category
`CQC(X)`.  When every `f φ` is flat, `(f φ)^*` is exact, and a *submodule* of a crystal is a
family of quasi-coherent subsheaves `G i ⊆ F i` with `α φ (f φ)^* (G i) = G i'` as subsheaves of
`F i'`.  A submodule is `κ`-generated when each `G i` is.

This file sets up that situation and proves that for the explicit cardinal `cardinalBound D`
attached to the system — infinite, at least the cardinality of `I` and of `Φ`, and at least the
size of every `X i` — the `κ`-generated submodules of any crystal form a directed system.

## Main definitions

* `SchemeSystem`: the datum `(I, Φ, j, X, f)` above.
* `SchemeSystem.IsFlat`: the hypothesis that every transition morphism is flat.
* `Crystal`: an object of `CQC(X)`, with `Crystal.Hom` and the category structure on it.
* `Crystal.transport φ G`: the subsheaf `α φ ((f φ)^* G)` of `F i'` attached to a subsheaf `G`
  of `F i`.  It is defined as an image subobject, and `Crystal.transport_eq_mk` identifies it
  with `α φ ((f φ)^* G)` itself once `(f φ)^*` preserves monomorphisms, which is what flatness
  of `f φ` supplies.
* `Subcrystal`: a submodule of a crystal, ordered componentwise.
* `Subcrystal.IsCardinalGenerated`: each component is `κ`-generated in the sense of Stacks 077L.
* `cardinalBound`: the cardinal attached to the system.

## Main results

* `imageSubobject_coprod_desc`: the image of `coprod.desc a b` is the join of the images of `a`
  and of `b`.  With `imageSubobject_epi_comp` (images are unchanged by precomposing with an
  epimorphism) this is what makes `transport` a join-preserving map of subobject lattices.
* `Crystal.transport_sup`, `Crystal.transport_bot` and `Crystal.transport_top`: `transport`
  preserves joins, the zero subsheaf and the whole module.  Preservation of joins uses only that
  `(f φ)^*` preserves epimorphisms and binary direct sums, both of which hold because it is a
  left adjoint.  Consequently the zero submodule and the crystal itself are submodules of the
  crystal, so `Subcrystal` is neither empty nor a proper notion by accident.
* `joinSubobject_eq_sup`: the join of two subobjects of a module on a scheme, computed as the
  image of the sum of their inclusions, is their join in the subobject lattice.  This transfers
  the quasi-coherence and the bound on generators proved for `joinSubobject` to `⊔`.
* `aleph0_le_cardinalBound`, `mk_I_le_cardinalBound`, `mk_Phi_le_cardinalBound`,
  `size_le_cardinalBound`, `mk_affineOpens_le_cardinalBound`, `mk_sections_le_cardinalBound`:
  the bounds satisfied by `cardinalBound D` by construction.
* `isFiltered_cardinalGeneratedSubcrystal`: **the directedness half of Stacks 077Z.**  For
  the cardinal `cardinalBound D`, which depends only on the system and not on the crystal, the
  `κ`-generated submodules of every crystal on a flat system form a directed system: the zero
  submodule is one, and the componentwise join of two is one.

## Where Stacks 077Z is proved

Tag 077Z asserts that there is a cardinal `κ` such that every object of `CQC(X)` *is the
directed colimit of* its `κ`-generated submodules.  Of the two halves of that conclusion this
file proves directedness, for the explicit `cardinalBound D`, and the attribute below is scoped
accordingly; the colimit half is
`Stacks.AlgebraicGeometry.Crystals.isColimit_cardinalGeneratedSubcrystalCocone`, and the two
together are the tag.

Four further files prove that half.  `CrystalColimit.lean` reduces it to the exhaustion — that
every section of `F i` over an affine open of `X i` is a section of a `κ`-generated submodule —
as `Stacks.AlgebraicGeometry.Crystals.isColimit_cardinalGeneratedSubcrystalCocone_of_exists_mem`.
`CrystalTransitionSection.lean` and `CrystalSaturation.lean` carry out the source's saturation
across the system: a family of sets of sections of the `F i` over the affine opens of the `X i`
is closed up, keeping the bound `κ`, under restriction between nested affine opens and under the
transitions of the system, which is
`Stacks.AlgebraicGeometry.Crystals.Crystal.exists_bounded_compatible_family`.
`CrystalFamilySubobject.lean` turns the restriction half of that compatibility into a
quasi-coherent `κ`-generated subsheaf `G i ⊆ F i` for each `i`, containing the prescribed
section, and `CrystalFamilyTransport.lean` turns the transition half into the condition
`transport φ (G i) = G i'`, which makes `G` a `Subcrystal` and supplies the exhaustion.

## References

* [Stacks Project, Tag 077Z](https://stacks.math.columbia.edu/tag/077Z)
* [Stacks Project, Tag 077L](https://stacks.math.columbia.edu/tag/077L)
* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
* [Stacks Project, Section 000H](https://stacks.math.columbia.edu/tag/000H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal AlgebraicGeometry
open Stacks.AlgebraicGeometry.CardinalGeneration

universe u

namespace Stacks.CategoryTheory.Subobject

variable {C : Type*} [Category C] [Abelian C]

/-- The canonical epimorphism onto an image subobject. -/
theorem epi_factorThruImageSubobject {X Y : C} (f : X ⟶ Y) :
    Epi (factorThruImageSubobject f) := by
  have h : factorThruImageSubobject f = factorThruImage f ≫ (imageSubobjectIso f).inv := by
    simp [factorThruImageSubobject]
  rw [h]
  exact @epi_comp _ _ _ _ _ _ inferInstance _ (IsIso.epi_of_iso _)

/-- The image subobject of a morphism is cut out by the inclusion of its abelian image. -/
theorem imageSubobject_eq_abelianImage {X Y : C} (f : X ⟶ Y) :
    imageSubobject f = _root_.CategoryTheory.Subobject.mk (Abelian.image.ι f) := by
  refine (_root_.CategoryTheory.Subobject.mk_eq_mk_of_comm (Abelian.image.ι f) (image.ι f)
    (Abelian.imageIsoImage f) ?_).symm
  simp only [Abelian.imageIsoImage, IsImage.isoExt_hom]
  exact IsImage.lift_fac _ _

/-- Precomposing with an epimorphism does not change the image subobject. -/
theorem imageSubobject_epi_comp {W X Y : C} (e : W ⟶ X) (he : Epi e) (g : X ⟶ Y) :
    imageSubobject (e ≫ g) = imageSubobject g := by
  have := he
  have : IsIso (image.preComp e g) := isIso_of_mono_of_epi _
  exact _root_.CategoryTheory.Subobject.mk_eq_mk_of_comm _ _ (asIso (image.preComp e g))
    (image.preComp_ι e g)

/-- The image subobject of a composite is at most the image subobject of the second factor. -/
theorem imageSubobject_comp_le' {A B Y : C} (h : A ⟶ B) (g : B ⟶ Y) :
    imageSubobject (h ≫ g) ≤ imageSubobject g :=
  imageSubobject_comp_le _ _

/-- **The image of a sum of two morphisms is the join of their images.** -/
theorem imageSubobject_coprod_desc {A B Y : C} (a : A ⟶ Y) (b : B ⟶ Y) :
    imageSubobject (coprod.desc a b) = imageSubobject a ⊔ imageSubobject b := by
  have hl := imageSubobject_comp_le' (coprod.inl : A ⟶ A ⨿ B) (coprod.desc a b)
  have hr := imageSubobject_comp_le' (coprod.inr : B ⟶ A ⨿ B) (coprod.desc a b)
  rw [coprod.inl_desc] at hl
  rw [coprod.inr_desc] at hr
  refine le_antisymm (imageSubobject_le _ (coprod.desc
    (factorThruImageSubobject a ≫ _root_.CategoryTheory.Subobject.ofLE _ _ le_sup_left)
    (factorThruImageSubobject b ≫ _root_.CategoryTheory.Subobject.ofLE _ _ le_sup_right))
    ?_) (sup_le hl hr)
  refine coprod.hom_ext ?_ ?_ <;>
    simp [_root_.CategoryTheory.Subobject.ofLE_arrow, imageSubobject_arrow_comp]

/-- Transporting an image subobject through a functor that preserves epimorphisms: the image of
the inclusion of the image of `h` agrees with the image of `h` itself. -/
theorem imageSubobject_map_arrow {D : Type*} [Category D] [Abelian D] (P : C ⥤ D)
    (hP : P.PreservesEpimorphisms) {F Z : C} (h : Z ⟶ F) {Y : D} (α : P.obj F ⟶ Y) :
    imageSubobject (P.map (imageSubobject h).arrow ≫ α) = imageSubobject (P.map h ≫ α) := by
  have he : Epi (factorThruImageSubobject h) := epi_factorThruImageSubobject h
  have he2 : Epi (P.map (factorThruImageSubobject h)) := hP.preserves _
  have key : P.map (factorThruImageSubobject h) ≫ P.map (imageSubobject h).arrow ≫ α
      = P.map h ≫ α := by
    rw [← Category.assoc, ← P.map_comp, imageSubobject_arrow_comp]
  rw [← key, imageSubobject_epi_comp _ he2]

/-- Transporting a join through a functor that preserves binary direct sums. -/
theorem imageSubobject_map_coprodComparison {D : Type*} [Category D] [Abelian D] (P : C ⥤ D)
    {A B F : C} (a : A ⟶ F) (b : B ⟶ F) {Y : D}
    (α : P.obj F ⟶ Y) [PreservesColimit (pair A B) P] :
    imageSubobject (P.map (coprod.desc a b) ≫ α)
      = imageSubobject (P.map a ≫ α) ⊔ imageSubobject (P.map b ≫ α) := by
  have hiso : IsIso (coprodComparison P A B) := by
    rw [← PreservesColimitPair.iso_hom]
    exact Iso.isIso_hom _
  have hc : coprodComparison P A B ≫ P.map (coprod.desc a b) ≫ α
      = coprod.desc (P.map a ≫ α) (P.map b ≫ α) := by
    refine coprod.hom_ext ?_ ?_
    · simp only [coprodComparison, coprod.inl_desc, ← Category.assoc, ← P.map_comp]
    · simp only [coprodComparison, coprod.inr_desc, ← Category.assoc, ← P.map_comp]
  rw [← imageSubobject_epi_comp (coprodComparison P A B) (IsIso.epi_of_iso _)
    (P.map (coprod.desc a b) ≫ α), hc, imageSubobject_coprod_desc]

end Stacks.CategoryTheory.Subobject

namespace Stacks.AlgebraicGeometry.Crystals

open Stacks.CategoryTheory.Subobject

/-! ### The join of two subobjects of a module on a scheme -/

/-- The image of the sum of the inclusions of two subobjects is their join. -/
private theorem imageSubobject_coprod_desc_arrow {C : Type*} [Category C] [Abelian C] {Y : C}
    (G H : Subobject Y) : imageSubobject (coprod.desc G.arrow H.arrow) = G ⊔ H := by
  rw [imageSubobject_coprod_desc, imageSubobject_mono, imageSubobject_mono,
    Subobject.mk_arrow, Subobject.mk_arrow]

/-- The join of two subobjects of an `𝒪_X`-module, computed in
`Stacks.AlgebraicGeometry.CardinalGeneration` as the image of the sum of their inclusions, is
their join in the subobject lattice. -/
theorem joinSubobject_eq_sup {X : Scheme.{u}} {F : X.Modules} (G H : Subobject F) :
    CardinalGeneration.joinSubobject G H = G ⊔ H := by
  rw [CardinalGeneration.joinSubobject, ← imageSubobject_eq_abelianImage,
    CardinalGeneration.joinDesc, imageSubobject_coprod_desc_arrow]

/-- The join of two quasi-coherent subobjects of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_sup {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]
    (G H : Subobject F) (hG : (G : X.Modules).IsQuasicoherent)
    (hH : (H : X.Modules).IsQuasicoherent) :
    ((G ⊔ H : Subobject F) : X.Modules).IsQuasicoherent := by
  rw [← joinSubobject_eq_sup]
  exact CardinalGeneration.isQuasicoherent_joinSubobject G H hG hH

/-- The join of two `κ`-generated subobjects is `κ`-generated, for `κ` infinite. -/
theorem isCardinalGenerated_sup {X : Scheme.{u}} {F : X.Modules} {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (G H : Subobject F)
    (hG : IsCardinalGenerated (R := X.ringCatSheaf) (G : X.Modules) κ)
    (hH : IsCardinalGenerated (R := X.ringCatSheaf) (H : X.Modules) κ) :
    IsCardinalGenerated (R := X.ringCatSheaf) ((G ⊔ H : Subobject F) : X.Modules) κ := by
  rw [← joinSubobject_eq_sup]
  exact CardinalGeneration.isCardinalGenerated_joinSubobject hκ G H hG hH

/-! ### The situation: a system of schemes and the crystals on it -/

/-- **A system of schemes** (Stacks 077Y): a set `I`, a set `Φ`, a pre-relation
`j : Φ → I × I`, a scheme `X i` for each `i ∈ I`, and for each `φ ∈ Φ` with `j φ = (i, i')` a
morphism of schemes `f φ : X i' ⟶ X i`.  No composability is required of the data. -/
structure SchemeSystem where
  /-- The index set of the schemes. -/
  I : Type u
  /-- The index set of the transition morphisms. -/
  Φ : Type u
  /-- The source and target indices of a transition morphism. -/
  j : Φ → I × I
  /-- The schemes of the system. -/
  X : I → Scheme.{u}
  /-- The transition morphisms, directed from the second index to the first. -/
  f : ∀ φ : Φ, X (j φ).2 ⟶ X (j φ).1

/-- The hypothesis of Stacks 077Z: every transition morphism of the system is flat. -/
class SchemeSystem.IsFlat (D : SchemeSystem.{u}) : Prop where
  /-- Every transition morphism is flat. -/
  flat : ∀ φ : D.Φ, Flat (D.f φ)

attribute [instance] SchemeSystem.IsFlat.flat

/-- **A crystal in quasi-coherent modules** on a system of schemes (Stacks 077Y): a
quasi-coherent module `F i` on each `X i` together with an isomorphism
`α φ : (f φ)^* (F i) ≅ F i'` for each `φ ∈ Φ` with `j φ = (i, i')`.  These are the objects of
the additive category `CQC(X)`. -/
structure Crystal (D : SchemeSystem.{u}) where
  /-- The module on each scheme of the system. -/
  F : ∀ i : D.I, (D.X i).Modules
  /-- Each module is quasi-coherent. -/
  isQuasicoherent : ∀ i, (F i).IsQuasicoherent
  /-- The comparison isomorphisms along the transition morphisms. -/
  α : ∀ φ : D.Φ, (Scheme.Modules.pullback (D.f φ)).obj (F (D.j φ).1) ≅ F (D.j φ).2

namespace Crystal

variable {D : SchemeSystem.{u}}

/-- A morphism of crystals: a morphism on each scheme of the system commuting with the
comparison isomorphisms. -/
@[ext]
structure Hom (M N : Crystal D) where
  /-- The component morphisms. -/
  hom : ∀ i, M.F i ⟶ N.F i
  /-- Compatibility with the comparison isomorphisms. -/
  comm : ∀ φ : D.Φ, (M.α φ).hom ≫ hom (D.j φ).2
    = (Scheme.Modules.pullback (D.f φ)).map (hom (D.j φ).1) ≫ (N.α φ).hom

/-- The category `CQC(X)` of crystals in quasi-coherent modules on the system. -/
instance : Category (Crystal D) where
  Hom := Hom
  id M := { hom := fun _ => 𝟙 _, comm := by intro φ; simp }
  comp g h :=
    { hom := fun i => g.hom i ≫ h.hom i
      comm := by
        intro φ
        rw [Functor.map_comp, ← Category.assoc, g.comm, Category.assoc, h.comm,
          ← Category.assoc] }
  id_comp _ := by ext i; simp
  comp_id _ := by ext i; simp
  assoc _ _ _ := by ext i; simp

variable (M : Crystal D)

/-- The pullback of a subsheaf `G ⊆ F i` to `X i'`, pushed into `F i'` along the comparison
isomorphism: the subsheaf `α φ ((f φ)^* G)` of the source's definition of a submodule of a
crystal.  It is taken as an image subobject so that it is defined without a flatness
hypothesis; `transport_eq_mk` shows that when `(f φ)^*` preserves monomorphisms — in particular
when `f φ` is flat — it is `α φ ((f φ)^* G)` itself. -/
def transport (φ : D.Φ) (G : Subobject (M.F (D.j φ).1)) : Subobject (M.F (D.j φ).2) :=
  imageSubobject ((Scheme.Modules.pullback (D.f φ)).map G.arrow ≫ (M.α φ).hom)

/-- For a flat transition morphism the pullback of the inclusion of a subsheaf of `F i`,
followed by the comparison isomorphism, is a monomorphism: `(f φ)^*` is exact. -/
instance mono_pullbackArrow [D.IsFlat] (φ : D.Φ) (G : Subobject (M.F (D.j φ).1)) :
    Mono ((Scheme.Modules.pullback (D.f φ)).map G.arrow ≫ (M.α φ).hom) := by
  have hlim : PreservesFiniteLimits (Scheme.Modules.pullback (D.f φ)) :=
    preservesFiniteLimits_modulesPullback_of_flat (D.f φ)
  have hmono : (Scheme.Modules.pullback (D.f φ)).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preservesFiniteLimits _
  have h1 : Mono ((Scheme.Modules.pullback (D.f φ)).map G.arrow) := hmono.preserves _
  have hi : Mono (M.α φ).hom := IsIso.mono_of_iso _
  exact mono_comp _ _

/-- For a flat transition morphism, `transport φ G` is the subsheaf `α φ ((f φ)^* G)` of `F i'`:
the pullback of the inclusion of `G` is again a monomorphism, so its image is cut out by it. -/
theorem transport_eq_mk [D.IsFlat] (φ : D.Φ) (G : Subobject (M.F (D.j φ).1)) :
    M.transport φ G
      = Subobject.mk ((Scheme.Modules.pullback (D.f φ)).map G.arrow ≫ (M.α φ).hom) :=
  imageSubobject_mono _

/-- `transport` carries the zero subsheaf to the zero subsheaf. -/
theorem transport_bot (φ : D.Φ) : M.transport φ ⊥ = ⊥ := by
  refine le_bot_iff.mp (imageSubobject_le _ 0 ?_)
  simp

/-- `transport` carries the whole of `F i` to the whole of `F i'`. -/
theorem transport_top (φ : D.Φ) : M.transport φ ⊤ = ⊤ := by
  have h1 : IsIso ((⊤ : Subobject (M.F (D.j φ).1)).arrow) :=
    Subobject.isIso_arrow_iff_eq_top _ |>.mpr rfl
  have h2 : IsIso ((Scheme.Modules.pullback (D.f φ)).map
      (⊤ : Subobject (M.F (D.j φ).1)).arrow ≫ (M.α φ).hom) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) (Iso.isIso_hom _)
  have h3 : Mono ((Scheme.Modules.pullback (D.f φ)).map
      (⊤ : Subobject (M.F (D.j φ).1)).arrow ≫ (M.α φ).hom) := IsIso.mono_of_iso _
  rw [transport, @imageSubobject_mono _ _ _ _ _ h3]
  exact @Subobject.mk_eq_top_of_isIso _ _ _ _ _ h2

/-- `transport` is monotone. -/
theorem transport_le (φ : D.Φ) {G H : Subobject (M.F (D.j φ).1)} (h : G ≤ H) :
    M.transport φ G ≤ M.transport φ H := by
  rw [transport, transport]
  refine imageSubobject_le _ ((Scheme.Modules.pullback (D.f φ)).map (Subobject.ofLE _ _ h) ≫
    factorThruImageSubobject ((Scheme.Modules.pullback (D.f φ)).map H.arrow ≫ (M.α φ).hom)) ?_
  rw [Category.assoc, imageSubobject_arrow_comp, ← Category.assoc, ← Functor.map_comp,
    Subobject.ofLE_arrow]

/-- **`transport` preserves joins.**  The join of two subsheaves is the image of the sum of
their inclusions, and `(f φ)^*` preserves epimorphisms and binary direct sums because it is a
left adjoint, so the image of the pullback of that sum is the join of the images. -/
theorem transport_sup (φ : D.Φ) (G H : Subobject (M.F (D.j φ).1)) :
    M.transport φ (G ⊔ H) = M.transport φ G ⊔ M.transport φ H := by
  have hP : (Scheme.Modules.pullback (D.f φ)).PreservesEpimorphisms := inferInstance
  rw [transport, ← imageSubobject_coprod_desc_arrow,
    imageSubobject_map_arrow (Scheme.Modules.pullback (D.f φ)) hP
      (coprod.desc G.arrow H.arrow) (M.α φ).hom,
    imageSubobject_map_coprodComparison (Scheme.Modules.pullback (D.f φ)) G.arrow H.arrow
      (M.α φ).hom]
  rfl

end Crystal

/-! ### Submodules of a crystal -/

variable {D : SchemeSystem.{u}}

/-- **A submodule of a crystal** in the sense of Stacks 077Z: a quasi-coherent subsheaf
`G i ⊆ F i` for every `i`, such that `α φ ((f φ)^* (G i)) = G i'` as subsheaves of `F i'` for
every `φ` with `j φ = (i, i')`. -/
@[ext]
structure Subcrystal [D.IsFlat] (M : Crystal D) where
  /-- The subsheaf of each component. -/
  sub : ∀ i : D.I, Subobject (M.F i)
  /-- Each component is quasi-coherent. -/
  isQuasicoherent : ∀ i, ((sub i : (D.X i).Modules)).IsQuasicoherent
  /-- The components are matched by the comparison isomorphisms. -/
  transport_sub : ∀ φ : D.Φ, M.transport φ (sub (D.j φ).1) = sub (D.j φ).2

namespace Subcrystal

variable [D.IsFlat] {M : Crystal D}

/-- Submodules of a crystal are ordered componentwise by inclusion of subsheaves. -/
instance : PartialOrder (Subcrystal M) where
  le N N' := ∀ i, N.sub i ≤ N'.sub i
  le_refl _ _ := le_rfl
  le_trans _ _ _ h h' i := (h i).trans (h' i)
  le_antisymm _ _ h h' := Subcrystal.ext (funext fun i => le_antisymm (h i) (h' i))

/-- `N ≤ N'` exactly when `N.sub i ≤ N'.sub i` for every `i`. -/
theorem le_def {N N' : Subcrystal M} : N ≤ N' ↔ ∀ i, N.sub i ≤ N'.sub i := Iff.rfl

/-- The zero submodule of a crystal. -/
instance : Bot (Subcrystal M) where
  bot :=
    { sub := fun _ => ⊥
      isQuasicoherent := fun i =>
        have h : IsInitial ((⊥ : Subobject (M.F i)) : (D.X i).Modules) :=
          IsInitial.ofIso initialIsInitial Subobject.botCoeIsoInitial.symm
        QuasicoherentColimits.isQuasicoherent_of_isColimit
          (D := Functor.empty (D.X i).Modules) (fun k => PEmpty.elim k.as) h
      transport_sub := fun φ => M.transport_bot φ }

/-- Each component of the zero submodule is `⊥`. -/
@[simp]
theorem bot_sub (i : D.I) : (⊥ : Subcrystal M).sub i = ⊥ := rfl

/-- A crystal is a submodule of itself: the comparison isomorphisms match the whole of `F i`
with the whole of `F i'`. -/
instance : Top (Subcrystal M) where
  top :=
    { sub := fun _ => ⊤
      isQuasicoherent := fun i =>
        have h : IsIso ((⊤ : Subobject (M.F i)).arrow) :=
          Subobject.isIso_arrow_iff_eq_top _ |>.mpr rfl
        (SheafOfModules.isQuasicoherent (D.X i).ringCatSheaf).prop_of_iso
          (@asIso _ _ _ _ ((⊤ : Subobject (M.F i)).arrow) h).symm (M.isQuasicoherent i)
      transport_sub := fun φ => M.transport_top φ }

/-- Each component of the top submodule is `⊤`. -/
@[simp]
theorem top_sub (i : D.I) : (⊤ : Subcrystal M).sub i = ⊤ := rfl

/-- The componentwise join of two submodules of a crystal is a submodule: `transport` preserves
joins. -/
def join (N N' : Subcrystal M) : Subcrystal M where
  sub i := N.sub i ⊔ N'.sub i
  isQuasicoherent i :=
    have := M.isQuasicoherent i
    isQuasicoherent_sup _ _ (N.isQuasicoherent i) (N'.isQuasicoherent i)
  transport_sub φ := by
    rw [M.transport_sup, N.transport_sub, N'.transport_sub]

/-- The components of `N.join N'` are the joins of the components of `N` and `N'`. -/
@[simp]
theorem join_sub (N N' : Subcrystal M) (i : D.I) :
    (N.join N').sub i = N.sub i ⊔ N'.sub i := rfl

/-- A submodule of a crystal lies below its join with another. -/
theorem le_join_left (N N' : Subcrystal M) : N ≤ N.join N' := fun _ => le_sup_left

/-- A submodule of a crystal lies below the join of another with it. -/
theorem le_join_right (N N' : Subcrystal M) : N' ≤ N.join N' := fun _ => le_sup_right

/-- A submodule of a crystal is `κ`-generated when each of its components is `κ`-generated in
the sense of Stacks 077L. -/
def IsCardinalGenerated (N : Subcrystal M) (κ : Cardinal.{u}) : Prop :=
  ∀ i : D.I, Stacks.AlgebraicGeometry.CardinalGeneration.IsCardinalGenerated
    (R := (D.X i).ringCatSheaf) ((N.sub i : (D.X i).Modules)) κ

/-- The zero submodule of a crystal is `κ`-generated for every cardinal `κ`. -/
theorem isCardinalGenerated_bot (κ : Cardinal.{u}) :
    (⊥ : Subcrystal M).IsCardinalGenerated κ := fun i =>
  CardinalGeneration.isCardinalGenerated_of_isZero
    (IsZero.of_iso (isZero_zero (D.X i).Modules) Subobject.botCoeIsoZero) _

/-- For an infinite cardinal `κ`, the join of two `κ`-generated submodules of a crystal is
`κ`-generated. -/
theorem isCardinalGenerated_join {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {N N' : Subcrystal M}
    (hN : N.IsCardinalGenerated κ) (hN' : N'.IsCardinalGenerated κ) :
    (N.join N').IsCardinalGenerated κ := fun i =>
  isCardinalGenerated_sup hκ _ _ (hN i) (hN' i)

end Subcrystal

/-! ### The cardinal attached to the system -/

/-- **The cardinal attached to a system of schemes.**  It is the maximum of `ℵ₀`, the
cardinalities of the index sets `I` and `Φ`, and the sizes (Stacks Section 000H) of the schemes of the
system.  These are the bounds the source's argument asks of the cardinal: `κ` infinite and
larger than the cardinality of `I` and of `Φ`, and, through the size of each `X i`, larger than
the number of affine opens of each `X i` and than the cardinality of the sections of its
structure sheaf over each of them. -/
def cardinalBound (D : SchemeSystem.{u}) : Cardinal.{u} :=
  max (max ℵ₀ (max #D.I #D.Φ)) (⨆ i : D.I, (D.X i).size)

/-- The cardinal attached to a system of schemes is infinite. -/
theorem aleph0_le_cardinalBound (D : SchemeSystem.{u}) : ℵ₀ ≤ cardinalBound D :=
  (le_max_left _ _).trans (le_max_left _ _)

/-- The cardinal attached to a system of schemes dominates the cardinality of `I`. -/
theorem mk_I_le_cardinalBound (D : SchemeSystem.{u}) : #D.I ≤ cardinalBound D :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)

/-- The cardinal attached to a system of schemes dominates the cardinality of `Φ`. -/
theorem mk_Phi_le_cardinalBound (D : SchemeSystem.{u}) : #D.Φ ≤ cardinalBound D :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)

/-- The cardinal attached to a system of schemes dominates the size of each of its schemes. -/
theorem size_le_cardinalBound (D : SchemeSystem.{u}) (i : D.I) :
    (D.X i).size ≤ cardinalBound D :=
  (le_ciSup bddAbove_of_small i).trans (le_max_right _ _)

/-- The cardinal attached to a system of schemes dominates the number of affine opens of each of
its schemes. -/
theorem mk_affineOpens_le_cardinalBound (D : SchemeSystem.{u}) (i : D.I) :
    #(D.X i).affineOpens ≤ cardinalBound D :=
  ((D.X i).mk_affineOpens_le_size).trans (size_le_cardinalBound D i)

/-- The cardinal attached to a system of schemes dominates the cardinality of the sections of
the structure sheaf of each of its schemes over each affine open. -/
theorem mk_sections_le_cardinalBound (D : SchemeSystem.{u}) (i : D.I)
    (U : (D.X i).affineOpens) : #Γ(D.X i, U.1) ≤ cardinalBound D :=
  ((D.X i).mk_sections_le_size U).trans (size_le_cardinalBound D i)

/-! ### Directedness -/

/-- The `κ`-generated submodules of a crystal. -/
abbrev CardinalGeneratedSubcrystal [D.IsFlat] (M : Crystal D) (κ : Cardinal.{u}) :=
  {N : Subcrystal M // N.IsCardinalGenerated κ}

/-- For an infinite cardinal `κ`, the `κ`-generated submodules of a crystal on a flat system of
schemes form a directed system: the zero submodule is one, and the componentwise join of two of
them is one. -/
theorem isFiltered_cardinalGeneratedSubcrystal_of_aleph0_le {D : SchemeSystem.{u}} [D.IsFlat]
    (M : Crystal D) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    IsFiltered (CardinalGeneratedSubcrystal M κ) where
  cocone_objs N N' :=
    ⟨⟨N.1.join N'.1, Subcrystal.isCardinalGenerated_join hκ N.2 N'.2⟩,
      homOfLE (Subcrystal.le_join_left N.1 N'.1), homOfLE (Subcrystal.le_join_right N.1 N'.1),
      trivial⟩
  cocone_maps _ N' _ _ := ⟨N', 𝟙 N', Subsingleton.elim _ _⟩
  nonempty := ⟨⟨⊥, Subcrystal.isCardinalGenerated_bot _⟩⟩

/-- **Stacks 077Z, the directedness half.**  For the cardinal `cardinalBound D`, which depends
only on the system of schemes and not on the crystal, the `cardinalBound D`-generated submodules
of every crystal on a flat system form a directed system.

This is one of the two declarations carrying the tag; the other,
`Stacks.AlgebraicGeometry.Crystals.isColimit_cardinalGeneratedSubcrystalCocone`, says that the
crystal is the colimit of that system.  Together they are the whole statement: for this `κ`
every object of `CQC(X)` is the directed colimit of its `κ`-generated submodules. -/
@[stacks 077Z "the directed system"]
instance isFiltered_cardinalGeneratedSubcrystal (D : SchemeSystem.{u}) [D.IsFlat]
    (M : Crystal D) : IsFiltered (CardinalGeneratedSubcrystal M (cardinalBound D)) :=
  isFiltered_cardinalGeneratedSubcrystal_of_aleph0_le M (aleph0_le_cardinalBound D)

end Stacks.AlgebraicGeometry.Crystals

end
