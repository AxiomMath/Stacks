module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.TensorProduct.Maps
import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
import StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal
import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Separation axioms for morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` with relative diagonal `Δ : X ⟶ X ×_Y X`. The morphism `f`
is *separated* when `Δ` is a closed immersion, and *quasi-separated* when `Δ` is
quasi-compact. Both conditions are stated for an arbitrary morphism of fppf sheaves on the big
fppf site of `S`.

## Main definitions

* `IsSeparatedMorphism`: the diagonal is a closed immersion.
* `IsQuasiSeparatedMorphism`: the diagonal is quasi-compact.
* `fppfYoneda`: the sheafified Yoneda embedding of the big fppf site of `S` into fppf sheaves,
  which is the Yoneda embedding since the site is subcanonical.
* `HasRelativeDiagonal`: for `P` a property of morphisms of schemes, the condition that every
  represented base change of the relative diagonal is a morphism of the site with `P`.
  Separatedness is the case `P = IsClosedImmersion`.

## Main results

* `isSeparatedMorphism_of_isPullback` and `isQuasiSeparatedMorphism_of_isPullback`: a base change
  of a separated, respectively quasi-separated, morphism is separated, respectively
  quasi-separated.
* `hasRelativeDiagonal_iff_forall_baseChange` and `isSeparatedMorphism_iff_forall_baseChange`: a
  relative diagonal condition, and separatedness, may be tested after base change to every scheme
  over the target.
* `hasRelativeDiagonal_iff_forall_affine_baseChange` and
  `isSeparatedMorphism_iff_forall_affine_baseChange`: a Zariski-local relative diagonal condition,
  and separatedness, hold exactly when the relative diagonal is relatively representable and the
  condition holds after base change to every affine scheme over the target.
* `hasRelativeDiagonal_iff_forall_affine_baseChange_of_isFormalAlgebraicSpace` and
  `isSeparatedMorphism_iff_forall_affine_baseChange_of_isFormalAlgebraicSpace`: the same with no
  representability conjunct, for a morphism whose source is a formal algebraic space.
* `isSeparatedMorphism_iff_isSeparated`: over an affine target, a morphism is separated exactly
  when its relative diagonal is relatively representable and its source is separated.
* `isSeparatedMorphism_iff_isSeparated_of_isFormalAlgebraicSpace`: the same with no
  representability conjunct, for a source which is a formal algebraic space.
* `isSeparatedMorphism_iff_forall_affine_baseChange_of_relativelyRepresentable_diag` and
  `isSeparatedMorphism_iff_isSeparated_of_relativelyRepresentable_diag`: the same two statements
  for a source whose absolute diagonal is relatively representable.
* `hasRelativeDiagonal_of_locallySurjective`, `isSeparatedMorphism_of_locallySurjective` and
  `hasRelativeDiagonal_of_locallySurjectiveFamily`: a relative diagonal condition, and
  separatedness, descend along a locally surjective morphism, or a jointly locally surjective
  family, onto the relative self-product.
* `exists_atlas_hasRelativeDiagonal_pullback_snd` and
  `exists_atlas_isSeparatedMorphism_pullback_snd`: a relative diagonal condition, and
  separatedness, hold after base change to every member of some covering of a formal algebraic
  space target.
* `hasRelativeDiagonal_of_atlas`, `hasRelativeDiagonal_of_atlas_of_isFormalAlgebraicSpace` and
  `isSeparatedMorphism_of_atlas`: conversely, a relative diagonal condition, and separatedness,
  hold as soon as they hold after base change to every member of a covering of the target.
* `isSeparatedMorphism_of_isAffineFormalAlgebraicSpace`: every morphism out of an affine formal
  algebraic space is separated.
* `isPullback_mapDesc`: the comparison `X ×_Z Y ⟶ X ×_T Y` of two fibre products is a base change
  of the relative diagonal of `Z ⟶ T`.
* `isSeparatedMorphism_mapDesc`: the comparison is separated.
* `isClosedImmersion_mapDesc`: the comparison is a closed immersion when `Z ⟶ T` is separated.
* `isQuasiCompactULift_mapDesc`: the comparison is quasi-compact when `Z ⟶ T` is quasi-separated.
* `relativelyRepresentable_mapDesc_of_isFormalAlgebraicSpace`,
  `relative_locallyOfFiniteType_mapDesc_of_isFormalAlgebraicSpace`,
  `relative_locallyQuasiFinite_mapDesc_of_isFormalAlgebraicSpace` and
  `relative_isSeparated_mapDesc_of_isFormalAlgebraicSpace`: for `Z` a formal algebraic space, the
  comparison is representable by schemes, locally of finite type, locally quasi-finite and
  separated.
* `isClosedImmersion_of_isIso`: an isomorphism of fppf sheaves is a closed immersion.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0GHY](https://stacks.math.columbia.edu/tag/0GHY)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
* [Stacks Project, Tag 0ARP](https://stacks.math.columbia.edu/tag/0ARP)
* [Stacks Project, Tag 0ARQ](https://stacks.math.columbia.edu/tag/0ARQ)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AN2](https://stacks.math.columbia.edu/tag/0AN2)
* [Stacks Project, Tag 0ARS](https://stacks.math.columbia.edu/tag/0ARS)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of formal algebraic spaces over `S` is *separated* when its relative diagonal
is a closed immersion, stated for an arbitrary morphism of fppf sheaves on the big fppf site
of `S`. -/
@[stacks 0ARN "part (1): separated", ega "I 10.15.1" "separated morphism"]
abbrev IsSeparatedMorphism {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  IsClosedImmersion B S hS (pullback.diagonal f)

/-- A morphism of formal algebraic spaces over `S` is *quasi-separated* when its relative
diagonal is quasi-compact, in the sense that every base change of that diagonal along a
morphism from a quasi-compact algebraic space has quasi-compact source. -/
abbrev IsQuasiSeparatedMorphism {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  Space.IsQuasiCompactULift.{u + 1} B S hS (pullback.diagonal f).hom

/-- Quasi-compactness of a morphism of presheaves on the big fppf site of `S` with values in
`Type (u + 1)` is stable under base change along a cartesian square. -/
private theorem isQuasiCompactULift_of_isPullback
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {k : F' ⟶ F} {a' : F' ⟶ G'} {a : F ⟶ G} {g : G' ⟶ G} (sq : IsPullback k a' a g)
    (ha : Space.IsQuasiCompactULift.{u + 1} B S hS a) :
    Space.IsQuasiCompactULift.{u + 1} B S hS a' := by
  intro Z hZalg hZqc ξ
  have hpb : IsPullback (pullback.fst ξ a') (pullback.snd ξ a' ≫ k) (ξ ≫ g) a :=
    ((IsPullback.of_hasPullback ξ a').flip.paste_horiz sq).flip
  exact Space.isQuasiCompactSpaceULift_of_iso B S hS hpb.isoPullback.symm
    (ha Z hZalg hZqc (ξ ≫ g))

/-- A base change of a separated morphism of formal algebraic spaces over `S` is separated: in a
cartesian square of fppf sheaves on the big fppf site of `S` whose right-hand column `f` is
separated, the left-hand column `snd` is separated. -/
@[stacks 0ARP "separated"]
theorem isSeparatedMorphism_of_isPullback {X Y Y' W : FppfSheaf B S hS}
    {fst : W ⟶ X} {snd : W ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback fst snd f g)
    (hf : IsSeparatedMorphism B S hS f) : IsSeparatedMorphism B S hS snd := by
  let Q : MorphismProperty (FppfSheaf B S hS) := fun _ _ h ↦ IsClosedImmersion B S hS h
  have hQ : Q.IsStableUnderBaseChange :=
    ⟨fun sq' hg ↦ isClosedImmersion_of_isPullback B S hS sq' hg⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q.diagonal) sq hf

/-- A base change of a quasi-separated morphism of fppf sheaves on the big fppf site of `S` is
quasi-separated. -/
theorem isQuasiSeparatedMorphism_of_isPullback {X Y Y' W : FppfSheaf B S hS}
    {fst : W ⟶ X} {snd : W ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback fst snd f g)
    (hf : IsQuasiSeparatedMorphism B S hS f) : IsQuasiSeparatedMorphism B S hS snd := by
  let Q : MorphismProperty (FppfSheaf B S hS) :=
    fun _ _ h ↦ Space.IsQuasiCompactULift.{u + 1} B S hS h.hom
  have hQ : Q.IsStableUnderBaseChange :=
    ⟨fun sq' hg ↦ isQuasiCompactULift_of_isPullback B S hS
      (sq'.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hg⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q.diagonal) sq hf

/-! ### Testing a separation axiom after base change -/

section Categorical

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]

/-- Relative representability of a morphism transports along a natural isomorphism of the
embedding functor. -/
private alias relativelyRepresentable_of_embedding_iso :=
  AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_natIso

/-- A relative morphism property transports along a natural isomorphism of the embedding
functor. -/
private theorem relative_of_embedding_iso {F G : C ⥤ D} (e : F ≅ G) (P : MorphismProperty C)
    {X Y : D} (f : X ⟶ Y) (hf : P.relative F f) : P.relative G f := by
  refine ⟨relativelyRepresentable_of_embedding_iso e f hf.rep, ?_⟩
  intro U V g p q hp
  apply hf.property ((e.app U).hom ≫ g) ((e.app V).hom ≫ p) q
  exact hp.of_iso (e.app V).symm (Iso.refl _) (e.app U).symm (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

variable [HasPullbacks D]

/-- In a category with fibre products, the relative diagonal of a base change of `f` along `g`
is itself a base change of the relative diagonal of `f`, taken along the canonical morphism
between the two relative self-products. -/
private theorem diagonal_isPullback_diagonal {X Y Y' : D} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    IsPullback (pullback.fst f g) (pullback.diagonal (pullback.snd f g)) (pullback.diagonal f)
      (pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
        (pullback.fst f g) g pullback.condition.symm pullback.condition.symm) := by
  let A := pullback f g
  let e : pullback (𝟙 A) (𝟙 A) ≅ A := asIso (pullback.fst (𝟙 A) (𝟙 A))
  let e' := pullback.congrHom (Category.id_comp (pullback.snd f g))
    (Category.id_comp (pullback.snd f g))
  have h := pullback_fst_map_snd_isPullback (f := f) (i := g) (i₁ := 𝟙 A) (i₂ := 𝟙 A)
  refine h.of_iso (e₁ := e) (e₂ := Iso.refl _) (e₃ := e') (e₄ := Iso.refl _)
    (fst' := pullback.fst f g) (snd' := pullback.diagonal (pullback.snd f g))
    (f' := pullback.diagonal f)
    (g' := pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
      (pullback.fst f g) g pullback.condition.symm pullback.condition.symm) ?_ ?_ ?_ ?_
  · simp [A, e]
  · apply pullback.hom_ext
    · simp only [e', pullback.congrHom_hom]
      rw [pullback.map_comp]
      dsimp [pullback.map]
      rw [pullback.lift_fst]
      simp [e, A]
    · simp only [e', pullback.congrHom_hom]
      rw [pullback.map_comp]
      dsimp [pullback.map]
      rw [pullback.lift_snd]
      simpa [e, A] using (pullback.condition (f := 𝟙 A) (g := 𝟙 A)).symm
  · simp
  · simp only [e', pullback.congrHom_hom]
    rw [← pullback.map_comp
      (X := A) (Y := A) (Z := Y')
      (X' := A) (Y' := A) (Z' := Y')
      (X'' := X) (Y'' := X) (Z'' := Y)
      (f := 𝟙 A ≫ pullback.snd f g) (g := 𝟙 A ≫ pullback.snd f g)
      (f' := pullback.snd f g) (g' := pullback.snd f g)
      (f'' := f) (g'' := f)
      (i₁ := 𝟙 A) (j₁ := pullback.fst f g)
      (i₂ := 𝟙 A) (j₂ := pullback.fst f g)
      (i₃ := 𝟙 Y') (j₃ := g)
      (e₁ := by cat_disch) (e₂ := by cat_disch)
      (e₃ := by simpa using (pullback.condition (f := f) (g := g)).symm)
      (e₄ := by simpa using (pullback.condition (f := f) (g := g)).symm)]
    simp only [Iso.refl_hom, Category.comp_id]
    rfl

/-- In a category with fibre products, the relative diagonal of a base change of `f` along `g`
is itself a base change of the relative diagonal of `f`, taken along the canonical morphism
between the two relative self-products. -/
alias diagonal_isPullback_diagonal' := diagonal_isPullback_diagonal

/-- A morphism of `D` satisfies a property of `C` relative to a functor `F : C ⥤ D` exactly
when each of its base changes along a morphism out of an object in the image of `F` does. -/
private theorem relative_iff_pullback_fst (F : C ⥤ D) (P : MorphismProperty C) {X Y : D}
    (f : X ⟶ Y) :
    P.relative F f ↔ ∀ (U : C) (g : F.obj U ⟶ Y), P.relative F (pullback.fst g f) := by
  constructor
  · intro hf U g
    exact (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback
      (IsPullback.of_hasPullback g f).flip hf
  · intro h
    refine ⟨?_, ?_⟩
    · intro U g
      let r := (h U g).rep
      refine ⟨r.pullback (𝟙 _), r.snd (𝟙 _), r.fst (𝟙 _) ≫ pullback.snd g f, ?_⟩
      simpa using (r.isPullback (𝟙 _)).paste_horiz (IsPullback.of_hasPullback g f).flip
    · intro U V g fst snd sq
      let k := pullback.lift (F.map snd) fst sq.w.symm
      apply (h U g).property (𝟙 _) k snd
      apply IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback g f).flip
      · simpa only [k, pullback.lift_snd, Category.id_comp] using sq
      · simp only [k, pullback.lift_fst, Category.comp_id]

/-- If the relative diagonal of every base change of `f` to an object in the image of a fully
faithful `F` has a property `P` relative to `F`, then so does the relative diagonal of `f`
itself. -/
private theorem relative_diagonal_of_pullback_diagonal (F : C ⥤ D) [F.Full] [F.Faithful]
    (P : MorphismProperty C) [P.RespectsIso] {X Y : D} (f : X ⟶ Y)
    (h : ∀ (U : C) (g : F.obj U ⟶ Y), P.relative F (pullback.diagonal (pullback.snd f g))) :
    P.relative F (pullback.diagonal f) := by
  apply MorphismProperty.relative.of_exists
  intro U a
  let g := a ≫ pullback.fst f f ≫ f
  let s : F.obj U ⟶ pullback f g := pullback.lift (a ≫ pullback.fst f f) (𝟙 _) (by simp [g])
  let t : F.obj U ⟶ pullback f g :=
    pullback.lift (a ≫ pullback.snd f f) (𝟙 _) (by
      simp only [g, Category.id_comp, Category.assoc]
      rw [pullback.condition])
  let b : F.obj U ⟶ pullback (pullback.snd f g) (pullback.snd f g) :=
    pullback.lift s t (by simp only [s, t, pullback.lift_snd])
  let c := pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
    (pullback.fst f g) g pullback.condition.symm pullback.condition.symm
  have hbc : b ≫ c = a := by
    apply pullback.hom_ext <;>
      simp only [b, c, s, t, Category.assoc, pullback.map, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.lift_fst]
  let hp := h U g
  let r := hp.rep
  refine ⟨r.pullback b, r.fst b ≫ pullback.fst f g, r.snd b, ?_, hp.property_snd b⟩
  have hc : IsPullback (r.fst b ≫ pullback.fst f g) (F.map (r.snd b))
      (pullback.diagonal f) (b ≫ c) :=
    (r.isPullback b).paste_horiz (diagonal_isPullback_diagonal f g)
  rwa [hbc] at hc

/-- A represented base change of the relative diagonal of `f` has a property `P` as soon as the
relative diagonal of every base change of `f` to the test object has `P` relative to `F`. -/
private theorem diagonal_property_of_baseChange (F : C ⥤ D) (P : MorphismProperty C)
    {X Y : D} (f : X ⟶ Y) {U V : C} (a : F.obj U ⟶ pullback f f) (p : F.obj V ⟶ X) (q : V ⟶ U)
    (sq : IsPullback p (F.map q) (pullback.diagonal f) a)
    (h : ∀ (g : F.obj U ⟶ Y), P.relative F (pullback.diagonal (pullback.snd f g))) : P q := by
  let g := a ≫ pullback.fst f f ≫ f
  let s : F.obj U ⟶ pullback f g := pullback.lift (a ≫ pullback.fst f f) (𝟙 _) (by simp [g])
  let t : F.obj U ⟶ pullback f g :=
    pullback.lift (a ≫ pullback.snd f f) (𝟙 _) (by
      simp only [g, Category.id_comp, Category.assoc]
      rw [pullback.condition])
  let b : F.obj U ⟶ pullback (pullback.snd f g) (pullback.snd f g) :=
    pullback.lift s t (by simp only [s, t, pullback.lift_snd])
  let c := pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
    (pullback.fst f g) g pullback.condition.symm pullback.condition.symm
  have hbc : b ≫ c = a := by
    apply pullback.hom_ext <;>
      simp only [b, c, s, t, Category.assoc, pullback.map, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.lift_fst]
  let k : F.obj V ⟶ pullback f g :=
    pullback.lift p (F.map q) (by
      have hh := congrArg (fun z ↦ z ≫ pullback.fst f f ≫ f) sq.w
      simpa [g, Category.assoc] using hh)
  apply (h g).property b k q
  apply IsPullback.of_right ?_ ?_ (diagonal_isPullback_diagonal f g)
  · show IsPullback (k ≫ pullback.fst f g) (F.map q) (pullback.diagonal f) (b ≫ c)
    rw [hbc]
    simpa only [k, pullback.lift_fst] using sq
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simpa [k, b, s, t, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc] using
          congrArg (fun z ↦ z ≫ pullback.fst f f) sq.w
      · simp [k, b, s, t, Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · apply pullback.hom_ext
      · simpa [k, b, s, t, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc] using
          congrArg (fun z ↦ z ≫ pullback.snd f f) sq.w
      · simp [k, b, s, t, Category.assoc, pullback.lift_snd]

section PullbacksInSource

variable [HasPullbacks C]

/-- A cartesian square of two scheme-valued points of `X` over a morphism `f : X ⟶ F.obj Z`
comes from the fibre product in `C` of the two induced morphisms to `Z`, and exhibits that
fibre product's comparison morphism as a base change of the relative diagonal of `f`. -/
private lemma pair_diagonal_square (F : C ⥤ D) [F.Faithful]
    [PreservesLimitsOfShape WalkingCospan F] {X : D} {Z U V W : C} (f : X ⟶ F.obj Z)
    (a : F.obj U ⟶ X) (b : F.obj V ⟶ X) (a₀ : U ⟶ Z) (b₀ : V ⟶ Z) (ha : F.map a₀ = a ≫ f)
    (hb : F.map b₀ = b ≫ f) (p : W ⟶ U) (q : W ⟶ V)
    (sq : IsPullback (F.map p) (F.map q) a b) :
    ∃ l : W ⟶ pullback a₀ b₀, l ≫ pullback.fst _ _ = p ∧ l ≫ pullback.snd _ _ = q ∧
      IsPullback (F.map p ≫ a) (F.map l) (pullback.diagonal f)
        (pullback.lift (F.map (pullback.fst a₀ b₀) ≫ a) (F.map (pullback.snd a₀ b₀) ≫ b) (by
          rw [Category.assoc, Category.assoc, ← ha, ← hb, ← F.map_comp, ← F.map_comp,
            pullback.condition])) := by
  have hpq : p ≫ a₀ = q ≫ b₀ := F.map_injective (by
    simp only [F.map_comp, ha, hb, ← Category.assoc, sq.w])
  let l := pullback.lift p q hpq
  refine ⟨l, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  have sp := (IsPullback.of_hasPullback a₀ b₀).map F
  apply IsPullback.mk'
  · apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
        Category.comp_id, pullback.lift_fst, pullback.lift_snd] <;>
      simp only [← Category.assoc, ← F.map_comp, l, pullback.lift_fst, pullback.lift_snd, sq.w]
  · intro T x y hx hy
    apply sq.hom_ext
    · have hh := congrArg (fun k => k ≫ F.map (pullback.fst a₀ b₀)) hy
      simpa only [Category.assoc, ← F.map_comp, l, pullback.lift_fst] using hh
    · have hh := congrArg (fun k => k ≫ F.map (pullback.snd a₀ b₀)) hy
      simpa only [Category.assoc, ← F.map_comp, l, pullback.lift_snd] using hh
  · intro T x y hxy
    have hx := congrArg (fun k => k ≫ pullback.fst f f) hxy
    have hy := congrArg (fun k => k ≫ pullback.snd f f) hxy
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
      pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hx hy
    let k := sq.lift (y ≫ F.map (pullback.fst a₀ b₀)) (y ≫ F.map (pullback.snd a₀ b₀))
      (by simpa only [Category.assoc] using hx.symm.trans hy)
    refine ⟨k, ?_, ?_⟩
    · simpa only [← Category.assoc, k, IsPullback.lift_fst] using hx.symm
    · apply sp.hom_ext <;>
        simp only [Category.assoc, ← F.map_comp, l, pullback.lift_fst, pullback.lift_snd, k,
          IsPullback.lift_fst, IsPullback.lift_snd]

/-- A cartesian square of two scheme-valued points of `X` over a morphism `f : X ⟶ F.obj Z`
comes from the fibre product in `C` of the two induced morphisms to `Z`, and exhibits that
fibre product's comparison morphism as a base change of the relative diagonal of `f`. -/
lemma pair_diagonal_square' (F : C ⥤ D) [F.Faithful]
    [PreservesLimitsOfShape WalkingCospan F] {X : D} {Z U V W : C} (f : X ⟶ F.obj Z)
    (a : F.obj U ⟶ X) (b : F.obj V ⟶ X) (a₀ : U ⟶ Z) (b₀ : V ⟶ Z) (ha : F.map a₀ = a ≫ f)
    (hb : F.map b₀ = b ≫ f) (p : W ⟶ U) (q : W ⟶ V)
    (sq : IsPullback (F.map p) (F.map q) a b) :
    ∃ l : W ⟶ pullback a₀ b₀, l ≫ pullback.fst _ _ = p ∧ l ≫ pullback.snd _ _ = q ∧
      IsPullback (F.map p ≫ a) (F.map l) (pullback.diagonal f)
        (pullback.lift (F.map (pullback.fst a₀ b₀) ≫ a) (F.map (pullback.snd a₀ b₀) ≫ b) (by
          rw [Category.assoc, Category.assoc, ← ha, ← hb, ← F.map_comp, ← F.map_comp,
            pullback.condition])) :=
  pair_diagonal_square F f a b a₀ b₀ ha hb p q sq

/-- When the relative diagonal of `f : X ⟶ F.obj Z` is relatively representable, the fibre
product of two scheme-valued points of `X` is itself represented by an object of `C`. -/
private lemma exists_pair_square (F : C ⥤ D) [F.Full] [F.Faithful]
    [PreservesLimitsOfShape WalkingCospan F] {X : D} {Z U V : C} (f : X ⟶ F.obj Z)
    (hr : F.relativelyRepresentable (pullback.diagonal f)) (a : F.obj U ⟶ X)
    (b : F.obj V ⟶ X) :
    ∃ (W : C) (p : W ⟶ U) (q : W ⟶ V), IsPullback (F.map p) (F.map q) a b := by
  let a₀ := F.preimage (a ≫ f)
  let b₀ := F.preimage (b ≫ f)
  let m := pullback.map a b (a ≫ f) (b ≫ f) (𝟙 _) (𝟙 _) f
    (Category.id_comp _).symm (Category.id_comp _).symm
  have hm : F.relativelyRepresentable m :=
    F.relativelyRepresentable.of_isPullback (pullback_map_diagonal_isPullback a b f) hr
  let e : F.obj (pullback a₀ b₀) ≅ pullback (a ≫ f) (b ≫ f) :=
    asIso (pullbackComparison F a₀ b₀) ≪≫
      pullback.congrHom (F.map_preimage _) (F.map_preimage _)
  have _ : IsIso (hm.fst e.hom) := (hm.isPullback e.hom).isIso_fst_of_isIso
  let i : F.obj (hm.pullback e.hom) ≅ pullback a b := asIso (hm.fst e.hom)
  refine ⟨hm.pullback e.hom, F.preimage (i.hom ≫ pullback.fst a b),
    F.preimage (i.hom ≫ pullback.snd a b), IsPullback.of_iso_pullback ⟨?_⟩ i ?_ ?_⟩
  · simp only [F.map_preimage, Category.assoc, pullback.condition]
  · exact (F.map_preimage _).symm
  · exact (F.map_preimage _).symm

/-- A represented base change of the relative diagonal of `f : X ⟶ F.obj Z` is itself a base
change, along a diagonal in `C`, of the comparison morphism into the fibre product in `C` of
the two induced morphisms to `Z`. -/
private lemma diagonal_test_pair_square (F : C ⥤ D) [F.Full] [F.Faithful]
    [PreservesLimitsOfShape WalkingCospan F] {X : D} {Z U V : C} (f : X ⟶ F.obj Z)
    (hr : F.relativelyRepresentable (pullback.diagonal f)) (γ : F.obj U ⟶ pullback f f)
    (t : F.obj V ⟶ X) (q : V ⟶ U) (hs : IsPullback t (F.map q) (pullback.diagonal f) γ) :
    ∃ (W : C) (p r : W ⟶ U) (a₀ : U ⟶ Z) (l : W ⟶ pullback a₀ a₀) (e : V ⟶ W),
      F.map a₀ = (γ ≫ pullback.fst f f) ≫ f ∧ F.map a₀ = (γ ≫ pullback.snd f f) ≫ f ∧
      l ≫ pullback.fst _ _ = p ∧ l ≫ pullback.snd _ _ = r ∧
      IsPullback (F.map p) (F.map r) (γ ≫ pullback.fst f f) (γ ≫ pullback.snd f f) ∧
      IsPullback e q l (pullback.diagonal a₀) := by
  let a := γ ≫ pullback.fst f f
  let b := γ ≫ pullback.snd f f
  let a₀ := F.preimage (a ≫ f)
  have ha : F.map a₀ = a ≫ f := F.map_preimage _
  have hb : F.map a₀ = b ≫ f := by
    rw [ha]
    simp only [a, b, Category.assoc, pullback.condition]
  obtain ⟨W, p, r, sq⟩ := exists_pair_square F f hr a b
  obtain ⟨l, hlp, hlr, sp⟩ := pair_diagonal_square F f a b a₀ a₀ ha hb p r sq
  let d := pullback.diagonal a₀
  let δ : F.obj (pullback a₀ a₀) ⟶ pullback f f :=
    pullback.lift (F.map (pullback.fst a₀ a₀) ≫ a) (F.map (pullback.snd a₀ a₀) ≫ b) (by
      simp only [Category.assoc, ← ha, ← hb, ← F.map_comp, pullback.condition])
  have hd : F.map d ≫ δ = γ := by
    apply pullback.hom_ext <;>
      simp only [δ, Category.assoc, pullback.lift_fst, pullback.lift_snd] <;>
      simp only [← Category.assoc, ← F.map_comp, d, pullback.diagonal_fst,
        pullback.diagonal_snd, F.map_id, Category.id_comp, a, b]
  have ht : t ≫ pullback.diagonal f = (F.map q ≫ F.map d) ≫ δ := by
    rw [Category.assoc, hd]
    exact hs.w
  let k := sp.lift t (F.map q ≫ F.map d) ht
  have he : F.map (F.preimage k) = k := F.map_preimage _
  refine ⟨W, p, r, a₀, l, F.preimage k, ha, hb, hlp, hlr, sq, ?_⟩
  apply IsPullback.of_map_of_faithful F
  apply IsPullback.of_right ?_ ?_ sp
  · show IsPullback (F.map (F.preimage k) ≫ (F.map p ≫ a)) (F.map q) (pullback.diagonal f)
      (F.map d ≫ δ)
    simpa only [he, k, IsPullback.lift_fst, hd] using hs
  · simpa only [he] using sp.lift_snd t (F.map q ≫ F.map d) ht

/-- A represented base change of the relative diagonal of `f : X ⟶ F.obj Z` is itself a base
change, along a diagonal in `C`, of the comparison morphism into the fibre product in `C` of
the two induced morphisms to `Z`. -/
alias diagonal_test_pair_square' := diagonal_test_pair_square

end PullbacksInSource

end Categorical

/-- The sheafified Yoneda embedding of the big fppf site of `S` into fppf sheaves. Since the
site is subcanonical this is the Yoneda embedding. -/
noncomputable abbrev fppfYoneda : BigFppfOver B S hS ⥤ FppfSheaf B S hS :=
  Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)

/-- The underlying presheaf of a sheafified representable is the universe-lifted Yoneda
presheaf, because the big fppf site of `S` is subcanonical. -/
private noncomputable def fppfYonedaCompSheafToPresheaf :
    fppfYoneda B S hS ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  Functor.isoWhiskerRight
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)) _ ≪≫
    (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf

/-- The underlying presheaf of a sheafified representable is the universe-lifted Yoneda
presheaf, because the big fppf site of `S` is subcanonical. -/
noncomputable def fppfYonedaCompSheafToPresheaf' :
    fppfYoneda B S hS ⋙ sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅
      uliftYoneda.{u + 1} (C := BigFppfOver B S hS) :=
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  Functor.isoWhiskerRight
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)) _ ≪≫
    (BigFppfOver.topology B S hS).uliftYonedaCompSheafToPresheaf

/-- A property of morphisms of the big fppf site of `S` is satisfied relative to the sheafified
Yoneda embedding by a morphism of fppf sheaves exactly when it is satisfied by the underlying
morphism of presheaves relative to the universe-lifted Yoneda embedding. -/
private theorem relative_fppfYoneda_iff_uliftYoneda
    (P : MorphismProperty (BigFppfOver B S hS)) {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    P.relative (fppfYoneda B S hS) f ↔ P.relative (uliftYoneda.{u + 1}) f.hom := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let L := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let _ : (fppfYoneda B S hS).Full :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  let _ : (fppfYoneda B S hS).Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).faithful
  constructor
  · intro h
    exact relative_of_embedding_iso (fppfYonedaCompSheafToPresheaf B S hS) P (L.map f)
      ((Space.relative_comp_map_iff (fppfYoneda B S hS) L P f).mpr h)
  · intro h
    exact (Space.relative_comp_map_iff (fppfYoneda B S hS) L P f).mp
      (relative_of_embedding_iso (fppfYonedaCompSheafToPresheaf B S hS).symm P (L.map f) h)

/-- A property of morphisms of the big fppf site of `S` is satisfied relative to the sheafified
Yoneda embedding by a morphism of fppf sheaves exactly when it is satisfied by the underlying
morphism of presheaves relative to the universe-lifted Yoneda embedding. -/
alias relative_fppfYoneda_iff_uliftYoneda' := relative_fppfYoneda_iff_uliftYoneda

/-- The sheafified Yoneda embedding of the big fppf site of `S` preserves fibre products. -/
private theorem fppfYoneda_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (fppfYoneda B S hS) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let L := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let _ : PreservesLimitsOfShape WalkingCospan (fppfYoneda B S hS ⋙ L) :=
    preservesLimitsOfShape_of_natIso (fppfYonedaCompSheafToPresheaf B S hS).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves (fppfYoneda B S hS) L

/-- The sheafified Yoneda embedding of the big fppf site of `S` preserves fibre products. -/
alias fppfYoneda_preservesPullbacks' := fppfYoneda_preservesPullbacks

/-- A relatively representable morphism of fppf sheaves has a Zariski-local property `P` of
morphisms of schemes relative to the sheafified Yoneda embedding as soon as every base change
of it to a sheaf represented by an *affine* object of the site has `P`. -/
private theorem relative_of_affine_test (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : (fppfYoneda B S hS).relativelyRepresentable f)
    (h : ∀ (U V : BigFppfOver B S hS) (g : (fppfYoneda B S hS).obj U ⟶ Y)
      (p : (fppfYoneda B S hS).obj V ⟶ X) (q : V ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsPullback p ((fppfYoneda B S hS).map q) f g →
      P ((BigFppfOver.toScheme B S hS).map q)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
      (fppfYoneda B S hS) f := by
  let _ : PreservesLimitsOfShape WalkingCospan (fppfYoneda B S hS) :=
    fppfYoneda_preservesPullbacks B S hS
  let T := BigFppfOver.toScheme B S hS
  refine ⟨hf, ?_⟩
  intro U V g p q sq
  show P (T.map q)
  apply IsZariskiLocalAtTarget.of_openCover (T.obj U).affineCover
  intro i
  let Ui : BigFppfOver B S hS :=
    Over.mk (X := B.obj hS)
      (⟨((T.obj U).affineCover.f i) ≫ U.hom.hom⟩ :
        (⟨(T.obj U).affineCover.X i,
          Scheme.size_lt_of_isOpenImmersion ((T.obj U).affineCover.f i)
            U.left.property⟩ : B.Schemes) ⟶ B.obj hS)
  let ui : Ui ⟶ U := Over.homMk ⟨(T.obj U).affineCover.f i⟩
  have hs := ((IsPullback.of_hasPullback q ui).map (fppfYoneda B S hS)).paste_horiz sq
  have hq : P (T.map (pullback.snd q ui)) :=
    h Ui (pullback q ui) ((fppfYoneda B S hS).map ui ≫ g)
      ((fppfYoneda B S hS).map (pullback.fst q ui) ≫ p) (pullback.snd q ui)
      (by change IsAffine ((T.obj U).affineCover.X i); infer_instance) hs
  have st : IsPullback (T.map (pullback.fst q ui)) (T.map (pullback.snd q ui))
      (T.map q) ((T.obj U).affineCover.f i) :=
    (IsPullback.of_hasPullback q ui).map T
  refine (P.arrow_mk_iso_iff (Arrow.isoMk st.isoPullback (Iso.refl _) ?_)).mp hq
  show st.isoPullback.hom ≫ pullback.snd (T.map q) ((T.obj U).affineCover.f i) =
    T.map (pullback.snd q ui) ≫ 𝟙 _
  rw [Category.comp_id]
  exact st.isoPullback_hom_snd

/-- A relatively representable morphism of fppf sheaves has a Zariski-local property `P` of
morphisms of schemes relative to the sheafified Yoneda embedding as soon as every base change
of it to a sheaf represented by an *affine* object of the site has `P`. -/
alias relative_of_affine_test' := relative_of_affine_test

/-- A morphism of fppf sheaves on the big fppf site of `S` is a closed immersion in the sense
of Stacks 0ANP exactly when it has the closed immersion property of schemes relative to the
sheafified Yoneda embedding, that is, when every represented base change of it is a closed
immersion of objects of the site. -/
private theorem isClosedImmersion_iff_relative {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsClosedImmersion B S hS f ↔
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS) f := by
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  rw [relative_fppfYoneda_iff_uliftYoneda]
  constructor
  · rintro ⟨_hrep, h⟩
    exact (relative_iff_pullback_fst (uliftYoneda.{u + 1}) P f.hom).mpr h
  · intro h
    refine ⟨?_, (relative_iff_pullback_fst (uliftYoneda.{u + 1}) P f.hom).mp h⟩
    intro U g
    exact Space.isAlgebraicSpaceULift_of_iso B S hS
      ((h.rep.isPullback g).isoPullback ≪≫ pullbackSymmetry f.hom g)
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (h.rep.pullback g))

/-- A morphism of fppf sheaves on the big fppf site of `S` has *relative diagonal* `P`, for `P`
a property of morphisms of schemes, when every base change of its relative diagonal along a
morphism out of a sheaf represented by an object of the site is a morphism of the site with
`P`. -/
abbrev HasRelativeDiagonal (P : MorphismProperty Scheme.{u}) {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) : Prop :=
  (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
    (fppfYoneda B S hS) (pullback.diagonal f)

/-- The separatedness axiom of Stacks 0ARN is the relative diagonal condition for the closed
immersion property of morphisms of schemes. -/
theorem isSeparatedMorphism_iff_hasRelativeDiagonal {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsSeparatedMorphism B S hS f ↔
      HasRelativeDiagonal B S hS
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) f :=
  isClosedImmersion_iff_relative B S hS (pullback.diagonal f)

/-- A base change of a morphism of fppf sheaves whose relative diagonal has `P` again has
relative diagonal `P`. -/
private theorem hasRelativeDiagonal_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X Y Y' W : FppfSheaf B S hS} {fst : W ⟶ X} {snd : W ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y} (sq : IsPullback fst snd f g) (hf : HasRelativeDiagonal B S hS P f) :
    HasRelativeDiagonal B S hS P snd := by
  let Q := (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
    (fppfYoneda B S hS)
  have hQ : Q.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q.diagonal) sq hf

/-- A morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` has relative diagonal `P`
exactly when, for every object `Z` of the site and every morphism from the sheaf it represents to
`Y`, the base change `Z ×_Y X ⟶ Z` of `f` has relative diagonal `P`. -/
@[stacks 0ARS "clauses (1) and (2): a relative diagonal condition holds for a morphism of \
formal algebraic spaces if and only if it holds for its base change to every scheme over the \
target"]
theorem hasRelativeDiagonal_iff_forall_baseChange (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    HasRelativeDiagonal B S hS P f ↔
      ∀ (U : BigFppfOver B S hS) (g : (fppfYoneda B S hS).obj U ⟶ Y),
        HasRelativeDiagonal B S hS P (pullback.snd f g) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : (fppfYoneda B S hS).Full :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  let _ : (fppfYoneda B S hS).Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).faithful
  refine ⟨fun hf U g ↦ hasRelativeDiagonal_of_isPullback B S hS P
    (IsPullback.of_hasPullback f g) hf, fun h ↦ ?_⟩
  exact relative_diagonal_of_pullback_diagonal (fppfYoneda B S hS)
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)) f h

/-- A morphism of fppf sheaves on the big fppf site of `S` is separated exactly when its base
change to every scheme over the target is separated. -/
@[stacks 0ARS "clauses (1) and (2) for separatedness: a morphism of formal algebraic spaces is \
separated if and only if its base change to every scheme over the target is separated"]
theorem isSeparatedMorphism_iff_forall_baseChange {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsSeparatedMorphism B S hS f ↔
      ∀ (U : BigFppfOver B S hS) (g : (fppfYoneda B S hS).obj U ⟶ Y),
        IsSeparatedMorphism B S hS (pullback.snd f g) :=
  (isSeparatedMorphism_iff_hasRelativeDiagonal B S hS f).trans
    ((hasRelativeDiagonal_iff_forall_baseChange B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) f).trans
      (forall_congr' fun _ ↦ forall_congr' fun _ ↦
        (isSeparatedMorphism_iff_hasRelativeDiagonal B S hS _).symm))

/-- A morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` has relative diagonal `P`,
for `P` a Zariski-local property of morphisms of schemes, exactly when its relative diagonal is
relatively representable and, for every *affine* object `Z` of the site and every morphism from
the sheaf it represents to `Y`, the base change `Z ×_Y X ⟶ Z` of `f` has relative diagonal
`P`. -/
@[stacks 0ARS "clauses (1) and (3): a Zariski-local relative diagonal condition holds for a \
morphism of formal algebraic spaces if and only if its relative diagonal is relatively \
representable and the condition holds for the base change to every affine scheme over the \
target"]
theorem hasRelativeDiagonal_iff_forall_affine_baseChange (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    HasRelativeDiagonal B S hS P f ↔
      (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f) ∧
        ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
          ∀ (g : (fppfYoneda B S hS).obj U ⟶ Y),
            HasRelativeDiagonal B S hS P (pullback.snd f g) := by
  refine ⟨fun hf ↦ ⟨hf.rep, fun U _ g ↦ hasRelativeDiagonal_of_isPullback B S hS P
    (IsPullback.of_hasPullback f g) hf⟩, fun ⟨hrep, h⟩ ↦ ?_⟩
  apply relative_of_affine_test B S hS P (pullback.diagonal f) hrep
  intro U V a p q hU sq
  exact diagonal_property_of_baseChange (fppfYoneda B S hS)
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)) f a p q sq
    (fun g ↦ h U hU g)

/-- A morphism of fppf sheaves on the big fppf site of `S` is separated exactly when its relative
diagonal is relatively representable and its base change to every affine scheme over the target
is separated. -/
@[stacks 0ARS "clauses (1) and (3) for separatedness: a morphism of formal algebraic spaces \
is separated if and only if its relative diagonal is relatively representable and its base \
change to every affine scheme over the target is separated"]
theorem isSeparatedMorphism_iff_forall_affine_baseChange {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsSeparatedMorphism B S hS f ↔
      (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f) ∧
        ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
          ∀ (g : (fppfYoneda B S hS).obj U ⟶ Y),
            IsSeparatedMorphism B S hS (pullback.snd f g) := by
  refine (isSeparatedMorphism_iff_hasRelativeDiagonal B S hS f).trans
    ((hasRelativeDiagonal_iff_forall_affine_baseChange B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) f).trans ?_)
  exact and_congr_right fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ (isSeparatedMorphism_iff_hasRelativeDiagonal B S hS _).symm

/-! ### Separatedness of a morphism to an affine scheme -/

/-- The map from the tensor product over `ℤ` of the coordinate rings of two schemes to that of
a third induced by a pair of morphisms factors through the map induced by a pair of morphisms
out of an intermediate scheme. -/
private lemma tensor_lift_comp {U V P W : Scheme.{u}} (l : W ⟶ P) (p : P ⟶ U) (q : P ⟶ V) :
    Algebra.TensorProduct.lift (l ≫ p).appTop.hom.toIntAlgHom
        (l ≫ q).appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _) =
      l.appTop.hom.toIntAlgHom.comp
        (Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom q.appTop.hom.toIntAlgHom
          (fun _ _ ↦ Commute.all _ _)) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp
  rfl

/-- For a fibre product of affine schemes over an affine base the canonical map from the tensor
product over `ℤ` of the coordinate rings of the two factors to the coordinate ring of the
fibre product is surjective. -/
private lemma tensor_lift_surjective_of_isPullback {U V Z P : Scheme.{u}} [IsAffine U]
    [IsAffine V] [IsAffine Z] {p : P ⟶ U} {q : P ⟶ V} {a : U ⟶ Z} {b : V ⟶ Z}
    (sq : IsPullback p q a b) :
    Function.Surjective (Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom
      q.appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  have _ : IsAffine P := IsAffine.of_isPullback sq
  let base := Γ(Z, ⊤)
  let left := Γ(U, ⊤)
  let right := Γ(V, ⊤)
  let result := Γ(P, ⊤)
  let _ : Algebra base left := a.appTop.hom.toAlgebra
  let _ : Algebra base right := b.appTop.hom.toAlgebra
  let _ : Algebra base result := (p.appTop.hom.comp a.appTop.hom).toAlgebra
  let _ : Algebra left result := p.appTop.hom.toAlgebra
  let _ : Algebra right result := q.appTop.hom.toAlgebra
  let _ : IsScalarTower base left result := .of_algebraMap_eq (by intros; rfl)
  let _ : IsScalarTower base right result := .of_algebraMap_eq (by
    intro element
    exact congrArg (fun morphism ↦ morphism.appTop.hom element) sq.w)
  let _ : Algebra.IsPushout base left right result :=
    CommRingCat.isPushout_iff_isPushout.mp (isPushout_appTop_of_isPullback sq)
  have heq : Algebra.TensorProduct.lift p.appTop.hom.toIntAlgHom q.appTop.hom.toIntAlgHom
      (fun _ _ ↦ Commute.all _ _) =
      ((Algebra.IsPushout.equiv base left right result).toAlgHom.restrictScalars ℤ).comp
        (Algebra.TensorProduct.mapOfCompatibleSMul base ℤ ℤ left right) := by
    apply Algebra.TensorProduct.ext'
    intro first second
    show _ = (Algebra.IsPushout.equiv base left right result) (first ⊗ₜ[base] second)
    rw [Algebra.IsPushout.equiv_tmul]
    simp [RingHom.algebraMap_toAlgebra]
  rw [heq]
  exact (Algebra.IsPushout.equiv base left right result).surjective.comp
    (Algebra.TensorProduct.mapOfCompatibleSMul_surjective base ℤ ℤ left right)

/-- For a fibre product of affine schemes over an affine base the canonical map from the tensor
product over `ℤ` of the coordinate rings of the two factors to the coordinate ring of the
fibre product is surjective. -/
alias tensor_lift_surjective_of_isPullback' := tensor_lift_surjective_of_isPullback

/-- A morphism of affine schemes is a closed immersion as soon as the map from the tensor
product over `ℤ` of the coordinate rings of two schemes it maps to is surjective. -/
private lemma isClosedImmersion_of_tensor_lift_surjective {U V P W : Scheme.{u}} [IsAffine P]
    [IsAffine W] (l : W ⟶ P) (p : P ⟶ U) (q : P ⟶ V)
    (h : Function.Surjective (Algebra.TensorProduct.lift (l ≫ p).appTop.hom.toIntAlgHom
      (l ≫ q).appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _))) :
    AlgebraicGeometry.IsClosedImmersion l := by
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [tensor_lift_comp] at h
  exact Function.Surjective.of_comp h

/-- A morphism `f : X ⟶ Z` of fppf sheaves on the big fppf site of `S` whose target is represented
by an affine scheme of the site is separated exactly when its relative diagonal is relatively
representable and the source `X` is separated as a single sheaf, in the sense of clause (2) of
Stacks 0AJ6: the fibre product over `X` of any two affine scheme-valued points of `X` is affine
with surjective comparison from the tensor product of their coordinate rings. -/
@[stacks 0ARS "clauses (3) and (4) for separatedness: a morphism of formal algebraic spaces \
to an affine scheme is separated if and only if its relative diagonal is relatively \
representable and its source is a separated formal algebraic space"]
theorem isSeparatedMorphism_iff_isSeparated {X : FppfSheaf B S hS} {Z : BigFppfOver B S hS}
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)) (f : X ⟶ (fppfYoneda B S hS).obj Z) :
    IsSeparatedMorphism B S hS f ↔
      (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f) ∧
        IsSeparated B S hS X := by
  let T := BigFppfOver.toScheme B S hS
  let F := fppfYoneda B S hS
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  let _ : F.Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).faithful
  let _ : PreservesLimitsOfShape WalkingCospan F := fppfYoneda_preservesPullbacks B S hS
  let _ := hZ
  refine (isSeparatedMorphism_iff_hasRelativeDiagonal B S hS f).trans ⟨fun hf ↦ ⟨hf.rep, ?_⟩,
    fun ⟨hr, h⟩ ↦ ?_⟩
  · intro U V P a b p q hU hV sq
    obtain ⟨l, hlp, hlq, sp⟩ := pair_diagonal_square F f a b (F.preimage (a ≫ f))
      (F.preimage (b ≫ f)) (F.map_preimage _) (F.map_preimage _) p q sq
    have hsq := (IsPullback.of_hasPullback (F.preimage (a ≫ f)) (F.preimage (b ≫ f))).map T
    let _ := hU
    let _ := hV
    have _ : IsAffine (T.obj (pullback (F.preimage (a ≫ f)) (F.preimage (b ≫ f)))) :=
      IsAffine.of_isPullback hsq
    have _ : AlgebraicGeometry.IsClosedImmersion (T.map l) := hf.property _ _ _ sp
    obtain ⟨hW, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (T.map l)
    refine ⟨hW, ?_⟩
    have hc : Function.Surjective (Algebra.TensorProduct.lift
        (T.map l ≫ T.map (pullback.fst (F.preimage (a ≫ f))
          (F.preimage (b ≫ f)))).appTop.hom.toIntAlgHom
        (T.map l ≫ T.map (pullback.snd (F.preimage (a ≫ f))
          (F.preimage (b ≫ f)))).appTop.hom.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
      rw [tensor_lift_comp]
      exact hsurj.comp (tensor_lift_surjective_of_isPullback hsq)
    simpa only [← T.map_comp, hlp, hlq] using hc
  · apply relative_of_affine_test B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (pullback.diagonal f) hr
    intro U V γ t q hU hs
    obtain ⟨W, p, r, a₀, l, e, ha, hb, hlp, hlr, sq, sp⟩ :=
      diagonal_test_pair_square F f hr γ t q hs
    obtain ⟨hW, hsurj⟩ := h U U W _ _ p r hU hU sq
    let _ := hU
    let _ := hW
    have hsq := (IsPullback.of_hasPullback a₀ a₀).map T
    have _ : IsAffine (T.obj (pullback a₀ a₀)) := IsAffine.of_isPullback hsq
    have hc : AlgebraicGeometry.IsClosedImmersion (T.map l) :=
      isClosedImmersion_of_tensor_lift_surjective (T.map l) (T.map (pullback.fst a₀ a₀))
        (T.map (pullback.snd a₀ a₀)) (by simpa only [← T.map_comp, hlp, hlr] using hsurj)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsClosedImmersion.{u}) (sp.map T) hc

/-- Every morphism of fppf sheaves on the big fppf site of `S` whose source is an affine
formal algebraic space is separated. -/
theorem isSeparatedMorphism_of_isAffineFormalAlgebraicSpace {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    IsSeparatedMorphism B S hS f :=
  (isSeparatedMorphism_iff_hasRelativeDiagonal B S hS f).mpr
    (relative_isClosedImmersion_pullback_diagonal_of_isAffineFormal B S hS f hX)

/-- A morphism of fppf sheaves whose source has relatively representable absolute diagonal is
separated exactly when its base change to every affine scheme over the target is separated. -/
@[stacks 0ARS "clauses (1) and (3) for separatedness with no extra conjunct, generalized past \
the source: the binder `hX` asks only that the absolute diagonal of the source be relatively \
representable, which every formal algebraic space satisfies by Stacks 0AIP, so the source's \
own case needs no such binder and is proved outright in \
`…isSeparatedMorphism_iff_forall_affine_baseChange_of_isFormalAlgebraicSpace`"]
theorem isSeparatedMorphism_iff_forall_affine_baseChange_of_relativelyRepresentable_diag
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : (fppfYoneda B S hS).relativelyRepresentable (diag X)) :
    IsSeparatedMorphism B S hS f ↔
      ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        ∀ (g : (fppfYoneda B S hS).obj U ⟶ Y),
          IsSeparatedMorphism B S hS (pullback.snd f g) :=
  (isSeparatedMorphism_iff_forall_affine_baseChange B S hS f).trans
    (and_iff_right (relativelyRepresentable_pullback_diagonal B S hS f hX))

/-- A morphism to an affine scheme out of a sheaf with relatively representable absolute
diagonal is separated exactly when that sheaf is separated. -/
@[stacks 0ARS "clauses (3) and (4) for separatedness with no extra conjunct, generalized past \
the source: the binder `hX` asks only that the absolute diagonal of the source be relatively \
representable, which every formal algebraic space satisfies by Stacks 0AIP, so the source's \
own case needs no such binder and is proved outright in \
`…isSeparatedMorphism_iff_isSeparated_of_isFormalAlgebraicSpace`"]
theorem isSeparatedMorphism_iff_isSeparated_of_relativelyRepresentable_diag
    {X : FppfSheaf B S hS} {Z : BigFppfOver B S hS}
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)) (f : X ⟶ (fppfYoneda B S hS).obj Z)
    (hX : (fppfYoneda B S hS).relativelyRepresentable (diag X)) :
    IsSeparatedMorphism B S hS f ↔ IsSeparated B S hS X :=
  (isSeparatedMorphism_iff_isSeparated B S hS hZ f).trans
    (and_iff_right (relativelyRepresentable_pullback_diagonal B S hS f hX))

/-- A morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` whose source is a formal
algebraic space is separated exactly when its base change to every affine scheme over the target is
separated. -/
@[stacks 0ARS "clauses (1) and (3) for separatedness, in the source's form with no extra \
conjunct: a morphism of formal algebraic spaces is separated if and only if its base change \
to every affine scheme over the target is separated"]
theorem isSeparatedMorphism_iff_forall_affine_baseChange_of_isFormalAlgebraicSpace
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) :
    IsSeparatedMorphism B S hS f ↔
      ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        ∀ (g : (fppfYoneda B S hS).obj U ⟶ Y),
          IsSeparatedMorphism B S hS (pullback.snd f g) :=
  isSeparatedMorphism_iff_forall_affine_baseChange_of_relativelyRepresentable_diag B S hS f
    (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)

/-- A morphism from a formal algebraic space to a sheaf represented by an affine scheme of the
site is separated exactly when its source is a separated formal algebraic space, separatedness of
a single sheaf being read as clause (2) of Stacks 0AJ6. -/
@[stacks 0ARS "clauses (3) and (4) for separatedness, in the source's form with no extra \
conjunct: a morphism from a formal algebraic space to an affine scheme is separated if and \
only if its source is a separated formal algebraic space"]
theorem isSeparatedMorphism_iff_isSeparated_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} {Z : BigFppfOver B S hS}
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)) (f : X ⟶ (fppfYoneda B S hS).obj Z)
    (hX : IsFormalAlgebraicSpace B S hS X) :
    IsSeparatedMorphism B S hS f ↔ IsSeparated B S hS X :=
  isSeparatedMorphism_iff_isSeparated_of_relativelyRepresentable_diag B S hS hZ f
    (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)

/-- A morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` whose source is a formal
algebraic space has relative diagonal `P`, for `P` a Zariski-local property of morphisms of
schemes, exactly when its base change to every affine scheme over the target has relative diagonal
`P`. -/
@[stacks 0ARS "clauses (1) and (3) for a relative diagonal condition, in the source's form \
with no extra conjunct: the condition holds for a morphism of formal algebraic spaces if and \
only if it holds for the base change to every affine scheme over the target"]
theorem hasRelativeDiagonal_iff_forall_affine_baseChange_of_isFormalAlgebraicSpace
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasRelativeDiagonal B S hS P f ↔
      ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        ∀ (g : (fppfYoneda B S hS).obj U ⟶ Y),
          HasRelativeDiagonal B S hS P (pullback.snd f g) :=
  (hasRelativeDiagonal_iff_forall_affine_baseChange B S hS P f).trans
    (and_iff_right (relativelyRepresentable_pullback_diagonal B S hS f
      (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)))

/-! ### Testing a separation axiom after a locally surjective base change -/

/-- Every sieve of the topology generated by the selected fppf covering families of a big fppf
site is refined by one selected covering family. -/
private theorem exists_covering_refinement_of_saturate {X : B.Schemes} {R : Sieve X}
    (hR : B.precoverage.Saturate X R) :
    ∃ E : PreZeroHypercover.{u + 1} X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R.arrows := by
  induction hR with
  | of X T hT =>
      change ∃ E : PreZeroHypercover.{u + 1} X, T = E.presieve₀ ∧ B.IsCovering ⟨X, E⟩ at hT
      obtain ⟨E, rfl, hE⟩ := hT
      exact ⟨E, hE, by simpa using Sieve.le_generate E.presieve₀⟩
  | top X =>
      refine ⟨PreZeroHypercover.singleton (𝟙 X), B.coverings_isSite.1 (𝟙 X), ?_⟩
      exact fun _ _ _ ↦ True.intro
  | pullback X R hR Y g ih =>
      obtain ⟨E, hE, hsub⟩ := ih
      obtain ⟨Pb, p₁, p₂, hpb, hP⟩ := B.coverings_isSite.2.2 ⟨X, E⟩ hE Y g
      refine ⟨⟨E.I₀, Pb, p₂⟩, hP, ?_⟩
      rintro Z k ⟨i⟩
      show R.arrows (p₂ i ≫ g)
      rw [← (hpb i).w]
      exact R.downward_closed (hsub (E.X i) (E.f i) ⟨i⟩) (p₁ i)
  | transitive X R T hR hT ihR ihT =>
      obtain ⟨E, hE, hEsub⟩ := ihR
      choose F hF hFsub using fun i ↦ ihT (hEsub _ _ ⟨i⟩)
      have hcomp : B.IsCovering ⟨X, E.bind F⟩ := by
        show CovBounded (IsFppfCovering (κ := B.cutoff)) B.coveringBound ⟨X, E.bind F⟩
        simpa [PreZeroHypercover.bind, PreZeroHypercover.pushforward] using
          B.coverings_isSite.2.1 ⟨X, E⟩ hE (fun i ↦ ⟨E.X i, F i⟩) hF fun _ ↦ rfl
      refine ⟨E.bind F, hcomp, ?_⟩
      rintro Z k ⟨⟨i, j⟩⟩
      show T.arrows ((F i).f j ≫ E.f i)
      exact hFsub i _ _ ⟨j⟩

/-- A property of morphisms of schemes which is stable under base change and local on the
target for the fppf topology descends, relative to the universe-lifted Yoneda embedding, along a
family `(b i)` of morphisms of presheaves which is jointly locally surjective, in the sense that
every scheme-valued section of the common target lifts, over every arrow of some covering sieve,
through a single member of the family. -/
private theorem relative_of_locallySurjectiveFamily_pullback (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {I : Type (u + 1)}
    {H : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : F ⟶ G) (b : ∀ i, H i ⟶ G)
    (ha : (uliftYoneda.{u + 1}).relativelyRepresentable a)
    (hb : ∀ (U : BigFppfOver B S hS) (ξ : G.obj (Opposite.op U)),
      ∃ R : Sieve U, R ∈ BigFppfOver.topology B S hS U ∧
        ∀ ⦃V : BigFppfOver B S hS⦄ (q : V ⟶ U), R q →
          ∃ (i : I) (t : (H i).obj (Opposite.op V)),
            (b i).app (Opposite.op V) t = G.map q.op ξ)
    (hbase : ∀ i, (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
      (uliftYoneda.{u + 1}) (pullback.snd a (b i))) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
      (uliftYoneda.{u + 1}) a := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage P T
  apply MorphismProperty.relative.of_exists (P := Q) (F := uliftYoneda.{u + 1})
  intro U g
  let ξ : G.obj (Opposite.op U) := uliftYonedaEquiv.{u + 1} g
  obtain ⟨R, hR, hRlift⟩ := hb U ξ
  have hcoverB' : (Sieve.overEquiv U) R ∈ B.precoverage.toGrothendieck U.left := by
    simpa [BigFppfSite.topology] using (B.topology.mem_over_iff _).mp hR
  obtain ⟨E, hE, hsub⟩ := exists_covering_refinement_of_saturate B
    (Precoverage.mem_toGrothendieck_iff.1 hcoverB')
  refine ⟨ha.pullback g, ha.fst g, ha.snd g, ha.isPullback g, ?_⟩
  let v := ha.snd g
  have hfppf : (E.map B.inclusion).presieve₀ ∈
      Scheme.fppfPrecoverage (B.inclusion.obj U.left) := by
    have hF : E.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion U.left :=
      B.isFppfCovering_of_isCovering hE
    rw [Precoverage.mem_comap_iff] at hF
    simpa [PreZeroHypercover.presieve₀_map] using hF
  show P (T.map v)
  apply (inferInstance : P.IsLocalAtTarget Scheme.fppfPrecoverage).of_forall_pullbackSnd hfppf
  intro Z k _ hk
  obtain ⟨i⟩ := hk
  let Ui : BigFppfOver B S hS := Over.mk (E.f i ≫ U.hom)
  let ui : Ui ⟶ U := Over.homMk (E.f i)
  obtain ⟨j, η, hηsec⟩ :=
    hRlift (V := Ui) ui ((Sieve.overEquiv_iff R (E.f i)).mp (hsub _ _ ⟨i⟩))
  let ηmap : (uliftYoneda.{u + 1}).obj Ui ⟶ H j := uliftYonedaEquiv.{u + 1}.symm η
  have hη : ηmap ≫ b j = uliftYoneda.map ui ≫ g := by
    apply (uliftYonedaEquiv.{u + 1} (X := Ui) (F := G)).injective
    simpa [ηmap, uliftYonedaEquiv_comp] using
      hηsec.trans (uliftYonedaEquiv_naturality g ui.op)
  let wv := pullback.fst v ui
  let wu := pullback.snd v ui
  let k' : (uliftYoneda.{u + 1}).obj (pullback v ui) ⟶ pullback a (b j) :=
    pullback.lift (uliftYoneda.map wv ≫ ha.fst g) (uliftYoneda.map wu ≫ ηmap) (by
      rw [Category.assoc, (ha.isPullback g).w, Category.assoc, hη, ← Category.assoc,
        ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
      exact congrArg (fun t ↦ uliftYoneda.map t ≫ g) (pullback.condition : wv ≫ v = wu ≫ ui))
  have hinner : IsPullback k' (uliftYoneda.map wu) (pullback.snd a (b j)) ηmap := by
    have htop := ((IsPullback.of_hasPullback v ui).map uliftYoneda).paste_horiz (ha.isPullback g)
    have hfst : k' ≫ pullback.fst a (b j) = uliftYoneda.map wv ≫ ha.fst g :=
      pullback.lift_fst _ _ _
    have hsnd : k' ≫ pullback.snd a (b j) = uliftYoneda.map wu ≫ ηmap :=
      pullback.lift_snd _ _ _
    have houter : IsPullback (k' ≫ pullback.fst a (b j)) (uliftYoneda.map wu) a (ηmap ≫ b j) := by
      rw [hfst, hη]
      exact htop
    exact IsPullback.of_right houter hsnd (IsPullback.of_hasPullback a (b j))
  have hloc : P (T.map wu) := (hbase j).property ηmap k' wu hinner
  have _ := (inferInstance : P.RespectsIso)
  have hui : T.map ui = (E.map B.inclusion).f i := rfl
  have _ : HasPullback (T.map v) (T.map ui) := by
    rw [hui]
    infer_instance
  have hschemePB := (IsPullback.of_hasPullback v ui).map T
  have he' : hschemePB.isoPullback.hom ≫
      pullback.snd (T.map v) ((E.map B.inclusion).f i) = T.map wu := by
    cases hui
    exact hschemePB.isoPullback_hom_snd
  refine (P.cancel_left_of_respectsIso hschemePB.isoPullback.hom _).mp ?_
  rw [he']
  exact hloc

/-- A base change of the relative diagonal along a morphism `b` of fppf sheaves has a property
`Q` relative to the sheafified Yoneda embedding exactly when the underlying morphism of presheaves
has it relative to the universe-lifted Yoneda embedding. -/
private theorem relative_pullback_snd_diagonal_hom
    (Q : MorphismProperty (BigFppfOver B S hS)) {X Y W : FppfSheaf B S hS} (f : X ⟶ Y)
    (b : W ⟶ pullback f f)
    (h : Q.relative (fppfYoneda B S hS) (pullback.snd (pullback.diagonal f) b)) :
    Q.relative (uliftYoneda.{u + 1}) (pullback.snd (pullback.diagonal f).hom b.hom) := by
  let L := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  have sq := (IsPullback.of_hasPullback (pullback.diagonal f) b).map L
  have he : Arrow.mk (pullback.snd (pullback.diagonal f) b).hom ≅
      Arrow.mk (pullback.snd (pullback.diagonal f).hom b.hom) :=
    Arrow.isoMk sq.isoPullback (Iso.refl _) (by
      change sq.isoPullback.hom ≫ pullback.snd (L.map (pullback.diagonal f)) (L.map b) =
        L.map (pullback.snd (pullback.diagonal f) b) ≫ 𝟙 _
      rw [Category.comp_id]
      exact sq.isoPullback_hom_snd)
  exact ((Q.relative (uliftYoneda.{u + 1})).arrow_mk_iso_iff he).mp
    ((relative_fppfYoneda_iff_uliftYoneda' B S hS Q _).mp h)

/-- A relative diagonal condition for an fppf-local property `P` of morphisms of schemes
descends along a locally surjective morphism `b` onto the relative self-product `X ×_Y X`: if the
base change of the relative diagonal of `f` along `b` has `P` relative to the site, and the
relative diagonal is relatively representable, then `f` has relative diagonal `P`. -/
@[stacks 0ARS "the descent step of clause (5): a relative diagonal condition descends along a \
single locally surjective morphism onto the relative self-product, which is the atlas clause \
with the covering of Definition 0AIM replaced by one locally surjective morphism, and is not \
the atlas form itself"]
theorem hasRelativeDiagonal_of_locallySurjective (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y W : FppfSheaf B S hS} (f : X ⟶ Y) (b : W ⟶ pullback f f)
    (hb : Sheaf.IsLocallySurjective b)
    (hrep : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f))
    (hbase : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
      (fppfYoneda B S hS) (pullback.snd (pullback.diagonal f) b)) :
    HasRelativeDiagonal B S hS P f := by
  let Q := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)
  have hrep' : (uliftYoneda.{u + 1}).relativelyRepresentable (pullback.diagonal f).hom :=
    ((relative_fppfYoneda_iff_uliftYoneda' B S hS ⊤ (pullback.diagonal f)).mp
      ⟨hrep, fun _ _ _ _ _ _ ↦ trivial⟩).rep
  refine (relative_fppfYoneda_iff_uliftYoneda' B S hS Q (pullback.diagonal f)).mpr ?_
  exact relative_of_locallySurjectiveFamily_pullback B S hS P (pullback.diagonal f).hom
    (fun _ : PUnit.{u + 2} ↦ b.hom) hrep'
    (fun U ξ ↦ ⟨_, hb.imageSieve_mem ξ, fun _ _ hq ↦ ⟨.unit, hq⟩⟩)
    fun _ ↦ relative_pullback_snd_diagonal_hom B S hS Q f b hbase

/-- Separatedness of a morphism of fppf sheaves whose relative diagonal is relatively representable
descends along a locally surjective morphism onto the relative self-product. -/
@[stacks 0ARS "the descent step of clause (5) for separatedness: separatedness descends along \
a single locally surjective morphism onto the relative self-product, which is the atlas clause \
with the covering of Definition 0AIM replaced by one locally surjective morphism, and is not \
the atlas form itself"]
theorem isSeparatedMorphism_of_locallySurjective {X Y W : FppfSheaf B S hS} (f : X ⟶ Y)
    (b : W ⟶ pullback f f) (hb : Sheaf.IsLocallySurjective b)
    (hrep : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f))
    (hbase : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS)
      (pullback.snd (pullback.diagonal f) b)) :
    IsSeparatedMorphism B S hS f := by
  have _ : MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact (isSeparatedMorphism_iff_hasRelativeDiagonal B S hS f).mpr
    (hasRelativeDiagonal_of_locallySurjective B S hS _ f b hb hrep hbase)

/-- A relative diagonal condition for an fppf-local property `P` of morphisms of schemes
descends along a *family* `(b i : W i ⟶ X ×_Y X)` of morphisms onto the relative self-product
whose induced morphism out of the coproduct is a surjection of sheaves: if the base change of the
relative diagonal of `f` along each `b i` has `P` relative to the site, and the relative diagonal
is relatively representable, then `f` has relative diagonal `P`. -/
@[stacks 0ARS "the descent step of clause (5) for a covering family: a relative diagonal \
condition descends along a family of morphisms onto the relative self-product whose induced \
morphism out of the coproduct is a surjection of sheaves"]
theorem hasRelativeDiagonal_of_locallySurjectiveFamily (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (I : Type (u + 1)) (W : I → FppfSheaf B S hS)
    (b : ∀ i, W i ⟶ pullback f f)
    (hb : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc b))
    (hrep : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f))
    (hbase : ∀ i, (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative
      (fppfYoneda B S hS) (pullback.snd (pullback.diagonal f) (b i))) :
    HasRelativeDiagonal B S hS P f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let Q := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)
  have hrep' : (uliftYoneda.{u + 1}).relativelyRepresentable (pullback.diagonal f).hom :=
    ((relative_fppfYoneda_iff_uliftYoneda' B S hS ⊤ (pullback.diagonal f)).mp
      ⟨hrep, fun _ _ _ _ _ _ ↦ trivial⟩).rep
  refine (relative_fppfYoneda_iff_uliftYoneda' B S hS Q (pullback.diagonal f)).mpr ?_
  refine relative_of_locallySurjectiveFamily_pullback B S hS P (pullback.diagonal f).hom
    (fun i ↦ (b i).hom) hrep' (fun U ξ ↦ ?_)
    fun i ↦ relative_pullback_snd_diagonal_hom B S hS Q f (b i) (hbase i)
  exact (Sheaf.isLocallySurjective_sigmaDesc_iff b).1 hb ξ

/-! ### Testing a separation axiom on a covering of the target -/

/-- If `Y` is a formal algebraic space and the morphism `f : X ⟶ Y` of fppf sheaves on the big fppf
site of `S` has relative diagonal `P`, then there is a covering `{Y_j ⟶ Y}` as in Definition 0AIM
such that the base change `Y_j ×_Y X ⟶ Y_j` of `f` has relative diagonal `P` for every `j`. -/
@[stacks 0ARS "clause (5) in the covering form of Definition 0AIM, necessity: a relative \
diagonal condition for a morphism of formal algebraic spaces holds for the base change to \
every member of some covering of the target as in Definition 0AIM"]
theorem exists_atlas_hasRelativeDiagonal_pullback_snd (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hf : HasRelativeDiagonal B S hS P f) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y),
      (∀ j, IsAffineFormalAlgebraicSpace B S hS (Yj j)) ∧
      (∀ j, ∃ hgj : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g j).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g j).hom hgj) ∧
      Sheaf.IsLocallySurjective (Sigma.desc g) ∧
      ∀ j, HasRelativeDiagonal B S hS P (pullback.snd f (g j)) := by
  obtain ⟨-, I, Yj, g, haffine, hetale, hsurj⟩ := hY
  exact ⟨I, Yj, g, haffine, hetale, hsurj, fun j ↦ hasRelativeDiagonal_of_isPullback B S hS P
    (IsPullback.of_hasPullback f (g j)) hf⟩

/-- If `Y` is a formal algebraic space and `f : X ⟶ Y` is separated then there is a covering
`{Y_j ⟶ Y}` as in Definition 0AIM along which every base change of `f` is separated. -/
@[stacks 0ARS "clause (5) in the covering form of Definition 0AIM, necessity for \
separatedness: a separated morphism of formal algebraic spaces has separated base change to \
every member of some covering of the target as in Definition 0AIM"]
theorem exists_atlas_isSeparatedMorphism_pullback_snd {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hf : IsSeparatedMorphism B S hS f) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    ∃ (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y),
      (∀ j, IsAffineFormalAlgebraicSpace B S hS (Yj j)) ∧
      (∀ j, ∃ hgj : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g j).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g j).hom hgj) ∧
      Sheaf.IsLocallySurjective (Sigma.desc g) ∧
      ∀ j, IsSeparatedMorphism B S hS (pullback.snd f (g j)) := by
  obtain ⟨-, I, Yj, g, haffine, hetale, hsurj⟩ := hY
  exact ⟨I, Yj, g, haffine, hetale, hsurj, fun j ↦ isSeparatedMorphism_of_isPullback B S hS
    (IsPullback.of_hasPullback f (g j)) hf⟩

/-- The comparison morphism from the fibre product of `Y_j ⟶ Y` with the relative
self-product `X ×_Y X` into the relative self-product of the base change `Y_j ×_Y X ⟶ Y_j`. -/
private noncomputable def atlasSelfProductComparison {X Y Y' : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Y' ⟶ Y) :
    pullback g (pullback.fst f f ≫ f) ⟶
      pullback (pullback.snd f g) (pullback.snd f g) :=
  pullback.lift
    (pullback.lift (pullback.snd g (pullback.fst f f ≫ f) ≫ pullback.fst f f)
      (pullback.fst g (pullback.fst f f ≫ f))
      (by rw [Category.assoc]; exact (pullback.condition (f := g)).symm))
    (pullback.lift (pullback.snd g (pullback.fst f f ≫ f) ≫ pullback.snd f f)
      (pullback.fst g (pullback.fst f f ≫ f))
      (by
        rw [Category.assoc, ← pullback.condition (f := f) (g := f)]
        exact (pullback.condition (f := g)).symm))
    (by rw [pullback.lift_snd, pullback.lift_snd])

/-- Composed with the canonical morphism `(Y_j ×_Y X) ×_{Y_j} (Y_j ×_Y X) ⟶ X ×_Y X`,
`atlasSelfProductComparison` is the projection `Y_j ×_Y (X ×_Y X) ⟶ X ×_Y X`. -/
private theorem atlasSelfProductComparison_comp {X Y Y' : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Y' ⟶ Y) :
    atlasSelfProductComparison B S hS f g ≫
        pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
          (pullback.fst f g) g pullback.condition.symm pullback.condition.symm =
      pullback.snd g (pullback.fst f f ≫ f) := by
  apply pullback.hom_ext <;>
    simp only [atlasSelfProductComparison, Category.assoc, pullback.map, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- The relative diagonal of `f` is a base change of the projection
`Y_j ×_Y (X ×_Y X) ⟶ X ×_Y X`, along `atlasSelfProductComparison` composed with the canonical
morphism `(Y_j ×_Y X) ×_{Y_j} (Y_j ×_Y X) ⟶ X ×_Y X`. -/
private theorem isPullback_diagonal_atlasSelfProductComparison {X Y Y' : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) :
    IsPullback (pullback.fst (pullback.diagonal f) (pullback.snd g (pullback.fst f f ≫ f)))
      (pullback.snd (pullback.diagonal f) (pullback.snd g (pullback.fst f f ≫ f)))
      (pullback.diagonal f)
      (atlasSelfProductComparison B S hS f g ≫
        pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
          (pullback.fst f g) g pullback.condition.symm pullback.condition.symm) := by
  rw [atlasSelfProductComparison_comp]
  exact IsPullback.of_hasPullback _ _

/-- Let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S` and let `P` be a
property of morphisms of schemes which is stable under base change and local on the target for
the fppf topology. If there is a family `{Y_j ⟶ Y}` whose induced morphism from the coproduct is
a surjection of sheaves — the covering condition of Definition 0AIM — such that every base change
`Y_j ×_Y X ⟶ Y_j` of `f` has relative diagonal `P`, and the relative diagonal of `f` is
relatively representable, then `f` has relative diagonal `P`. -/
@[stacks 0ARS "clause (5) in the covering form of Definition 0AIM, sufficiency for a relative \
diagonal condition: the condition holds for a morphism of formal algebraic spaces with \
relatively representable relative diagonal as soon as it holds for the base change to every \
member of a covering of the target as in Definition 0AIM"]
theorem hasRelativeDiagonal_of_atlas (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc g))
    (hrep : (fppfYoneda B S hS).relativelyRepresentable (pullback.diagonal f))
    (hP : ∀ j, HasRelativeDiagonal B S hS P (pullback.snd f (g j))) :
    HasRelativeDiagonal B S hS P f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine hasRelativeDiagonal_of_locallySurjectiveFamily B S hS P f I
    (fun j ↦ pullback (g j) (pullback.fst f f ≫ f))
    (fun j ↦ pullback.snd (g j) (pullback.fst f f ≫ f))
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (pullback.fst f f ≫ f) g hsurj)
    hrep (fun j ↦ ?_)
  exact (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))).of_isPullback
    (IsPullback.of_right' (isPullback_diagonal_atlasSelfProductComparison B S hS f (g j))
      (diagonal_isPullback_diagonal' f (g j))) (hP j)

/-- A morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` whose source is a formal
algebraic space has relative diagonal `P` as soon as its base change to every member of some
covering of the target as in Definition 0AIM does. -/
@[stacks 0ARS "clause (5) in the covering form of Definition 0AIM, sufficiency for a relative \
diagonal condition, in the source's form with no extra conjunct: the condition holds for a \
morphism of formal algebraic spaces as soon as it holds for the base change to every member of \
a covering of the target as in Definition 0AIM"]
theorem hasRelativeDiagonal_of_atlas_of_isFormalAlgebraicSpace (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc g))
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hP : ∀ j, HasRelativeDiagonal B S hS P (pullback.snd f (g j))) :
    HasRelativeDiagonal B S hS P f :=
  hasRelativeDiagonal_of_atlas B S hS P f I Yj g hsurj
    (relativelyRepresentable_pullback_diagonal B S hS f
      (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hX)) hP

/-- Let `f : X ⟶ Y` be a morphism of fppf sheaves on the big fppf site of `S`. If there is a family
`{Y_j ⟶ Y}` whose induced morphism from the coproduct is a surjection of sheaves — which is the
covering condition of Definition 0AIM — such that every base change `Y_j ×_Y X ⟶ Y_j` of `f` is
separated, then `f` is separated. -/
@[stacks 0ARS "clause (5) in the covering form of Definition 0AIM, sufficiency for \
separatedness: a morphism of formal algebraic spaces is separated as soon as its base change \
to every member of a covering of the target as in Definition 0AIM is separated"]
theorem isSeparatedMorphism_of_atlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (I : Type (u + 1)) (Yj : I → FppfSheaf B S hS) (g : ∀ j, Yj j ⟶ Y)
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc g))
    (hsep : ∀ j, IsSeparatedMorphism B S hS (pullback.snd f (g j))) :
    IsSeparatedMorphism B S hS f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine isClosedImmersion_of_locallySurjectiveFamily B S hS I
    (fun j ↦ pullback (g j) (pullback.fst f f ≫ f))
    (fun j ↦ pullback.snd (g j) (pullback.fst f f ≫ f))
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (pullback.fst f f ≫ f) g hsurj)
    (fun j ↦ ?_)
  exact isClosedImmersion_of_isPullback B S hS
    (IsPullback.of_right' (isPullback_diagonal_atlasSelfProductComparison B S hS f (g j))
      (diagonal_isPullback_diagonal' f (g j))) (hsep j)

/-! ### The comparison of two fibre products -/

section MapDesc

variable {X Y Z T : FppfSheaf B S hS}

/-- The *magic diagram*: for morphisms `f : X ⟶ Z`, `g : Y ⟶ Z` and `h : Z ⟶ T` of fppf sheaves
on the big fppf site of `S`, the canonical comparison `X ×_Z Y ⟶ X ×_T Y` is a base change of
the relative diagonal of `h`, along the morphism `X ×_T Y ⟶ Z ×_T Z` induced by `f` and `g`. -/
theorem isPullback_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    IsPullback (pullback.fst f g ≫ f) (pullback.mapDesc f g h) (pullback.diagonal h)
      (pullback.map (f ≫ h) (g ≫ h) h h f g (𝟙 T) (Category.comp_id _) (Category.comp_id _)) :=
  pullback_map_diagonal_isPullback f g h

/-- An isomorphism of presheaves on the big fppf site of `S` has the closed immersion property
of morphisms of schemes relative to the universe-lifted Yoneda embedding. -/
private theorem relative_isClosedImmersion_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F ⟶ G) [IsIso e] :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) e := by
  refine ⟨Functor.relativelyRepresentable.of_isIso _ _, ?_⟩
  intro A C g fst snd hpb
  have _ : IsIso ((uliftYoneda.{u + 1}).map snd) := hpb.isIso_snd_of_isIso
  have _ : IsIso snd :=
    Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) snd
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map snd) := inferInstance
  show AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- An isomorphism of fppf sheaves on the big fppf site of `S` is a closed immersion in the
sense of Stacks 0ANP. -/
theorem isClosedImmersion_of_isIso (e : X ⟶ Y) [IsIso e] : IsClosedImmersion B S hS e := by
  have _ : IsIso e.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).map e))
  have hfst : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj),
      IsIso (pullback.fst ξ e.hom) :=
    fun U ξ ↦ (IsPullback.of_hasPullback ξ e.hom).isIso_fst_of_isIso
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS e.hom := by
    intro U ξ
    have _ := hfst U ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS (asIso (pullback.fst ξ e.hom)).symm
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS U)
  refine ⟨hrep, fun U ξ ↦ ?_⟩
  have _ := hfst U ξ
  exact relative_isClosedImmersion_of_isIso B S hS (pullback.fst ξ e.hom)

/-- The comparison `X ×_Z Y ⟶ X ×_T Y` of two fibre products of fppf sheaves on the big fppf
site of `S` is separated in the sense of Stacks 0ARN. -/
@[stacks 0ARQ "part (1): separated, separatedness read in the sense of Stacks 0ARN"]
theorem isSeparatedMorphism_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    IsSeparatedMorphism B S hS (pullback.mapDesc f g h) := by
  have _ : Mono (pullback.mapDesc f g h) := pullback.mono_mapDesc f g h
  have _ : IsIso (pullback.diagonal (pullback.mapDesc f g h)) := inferInstance
  exact isClosedImmersion_of_isIso B S hS _

/-- If the absolute diagonal of `Z` is relatively representable, then so is the comparison
`X ×_Z Y ⟶ X ×_T Y`. -/
-- NO 0ARQ attribute: this clause carries 0AIP for `diag Z` as a hypothesis, and it is
-- near-circular: with `T` terminal and `f = g = 𝟙_Z` the conclusion coincides with the
-- hypothesis up to `pullback (𝟙 Z) (𝟙 Z) ≅ Z`. The unconditional affine-`Z` and general
-- formal-`Z` forms below carry the tag instead.
theorem relativelyRepresentable_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hZ : (fppfYoneda B S hS).relativelyRepresentable (diag Z)) :
    (fppfYoneda B S hS).relativelyRepresentable (pullback.mapDesc f g h) :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange (fppfYoneda B S hS)).of_isPullback
    (isPullback_mapDesc B S hS f g h) (relativelyRepresentable_pullback_diagonal B S hS h hZ)

/-- If every represented base change of the absolute diagonal of `Z` is a morphism of the site
with `Q`, then so is every represented base change of the comparison `X ×_Z Y ⟶ X ×_T Y`. -/
-- NO 0ARQ attribute, for the same two reasons as the clause above: it carries 0AIP for
-- `diag Z` as a hypothesis, and is near-circular in the degenerate instantiation. The
-- unconditional affine-`Z` and general formal-`Z` forms below carry the tag.
theorem relative_mapDesc (Q : MorphismProperty (BigFppfOver B S hS)) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) (hZ : Q.relative (fppfYoneda B S hS) (diag Z)) :
    Q.relative (fppfYoneda B S hS) (pullback.mapDesc f g h) :=
  (MorphismProperty.relative_isStableUnderBaseChange Q).of_isPullback
    (isPullback_mapDesc B S hS f g h) (relative_pullback_diagonal B S hS Q h hZ)

/-- When `Z` is an *affine* formal algebraic space, the comparison `X ×_Z Y ⟶ X ×_T Y` is
representable by schemes. -/
@[stacks 0ARQ "part (1): representable by schemes, unconditionally for Z an affine formal \
algebraic space"]
theorem relativelyRepresentable_mapDesc_of_isAffineFormal (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hZ : IsAffineFormalAlgebraicSpace B S hS Z) :
    (fppfYoneda B S hS).relativelyRepresentable (pullback.mapDesc f g h) :=
  relativelyRepresentable_mapDesc B S hS f g h
    (relativelyRepresentable_diag_of_isAffineFormal B S hS hZ)

/-- When `Z` is an *affine* formal algebraic space, every represented base change of the
comparison `X ×_Z Y ⟶ X ×_T Y` is a locally quasi-finite, locally of finite type morphism of
schemes. -/
@[stacks 0ARQ "part (1): locally quasi-finite, unconditionally for Z an affine formal \
algebraic space"]
theorem relative_locallyQuasiFinite_mapDesc_of_isAffineFormal (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) (hZ : IsAffineFormalAlgebraicSpace B S hS Z) :
    (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS)
      (pullback.mapDesc f g h) :=
  relative_mapDesc B S hS _ f g h
    (relative_locallyQuasiFinite_diag_of_isAffineFormal B S hS hZ)

/-- When `Z` is an *affine* formal algebraic space, every represented base change of the
comparison `X ×_Z Y ⟶ X ×_T Y` is a locally of finite type morphism of schemes. -/
@[stacks 0ARQ "part (1): locally of finite type, unconditionally for Z an affine formal \
algebraic space"]
theorem relative_locallyOfFiniteType_mapDesc_of_isAffineFormal (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) (hZ : IsAffineFormalAlgebraicSpace B S hS Z) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS)
      (pullback.mapDesc f g h) :=
  relative_mapDesc B S hS _ f g h
    (relative_locallyOfFiniteType_diag_of_isAffineFormal B S hS hZ)

/-- When `Z` is an *affine* formal algebraic space, every represented base change of the
comparison `X ×_Z Y ⟶ X ×_T Y` is a separated morphism of schemes. -/
@[stacks 0ARQ "part (1): separated in the represented-base-change sense of Stacks 0AN2, \
unconditionally for Z an affine formal algebraic space"]
theorem relative_isSeparated_mapDesc_of_isAffineFormal (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hZ : IsAffineFormalAlgebraicSpace B S hS Z) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS)
      (pullback.mapDesc f g h) :=
  relative_mapDesc B S hS _ f g h (relative_isSeparated_diag_of_isAffineFormal B S hS hZ)

/-- When `Z` is a formal algebraic space, the comparison `X ×_Z Y ⟶ X ×_T Y` is representable
by schemes. -/
@[stacks 0ARQ "part (1): representable by schemes, for Z an arbitrary formal algebraic space"]
theorem relativelyRepresentable_mapDesc_of_isFormalAlgebraicSpace (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) (hZ : IsFormalAlgebraicSpace B S hS Z) :
    (fppfYoneda B S hS).relativelyRepresentable (pullback.mapDesc f g h) :=
  relativelyRepresentable_mapDesc B S hS f g h
    (relativelyRepresentable_diag_of_isFormalAlgebraicSpace B S hS hZ)

/-- When `Z` is a formal algebraic space, every represented base change of the comparison
`X ×_Z Y ⟶ X ×_T Y` is a locally quasi-finite, locally of finite type morphism of schemes. -/
@[stacks 0ARQ "part (1): locally quasi-finite, for Z an arbitrary formal algebraic space"]
theorem relative_locallyQuasiFinite_mapDesc_of_isFormalAlgebraicSpace (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) (hZ : IsFormalAlgebraicSpace B S hS Z) :
    (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS)
      (pullback.mapDesc f g h) :=
  relative_mapDesc B S hS _ f g h
    (relative_locallyQuasiFinite_diag_of_isFormalAlgebraicSpace B S hS hZ)

/-- When `Z` is a formal algebraic space, every represented base change of the comparison
`X ×_Z Y ⟶ X ×_T Y` is a locally of finite type morphism of schemes. -/
@[stacks 0ARQ "part (1): locally of finite type, for Z an arbitrary formal algebraic space"]
theorem relative_locallyOfFiniteType_mapDesc_of_isFormalAlgebraicSpace (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) (hZ : IsFormalAlgebraicSpace B S hS Z) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS)
      (pullback.mapDesc f g h) :=
  relative_mapDesc B S hS _ f g h
    (relative_locallyOfFiniteType_diag_of_isFormalAlgebraicSpace B S hS hZ)

/-- When `Z` is a formal algebraic space, every represented base change of the comparison
`X ×_Z Y ⟶ X ×_T Y` is a separated morphism of schemes. -/
@[stacks 0ARQ "part (1): separated in the represented-base-change sense of Stacks 0AN2, for Z \
an arbitrary formal algebraic space"]
theorem relative_isSeparated_mapDesc_of_isFormalAlgebraicSpace (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) (hZ : IsFormalAlgebraicSpace B S hS Z) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (fppfYoneda B S hS)
      (pullback.mapDesc f g h) :=
  relative_mapDesc B S hS _ f g h
    (relative_isSeparated_diag_of_isFormalAlgebraicSpace B S hS hZ)

/-- If `h : Z ⟶ T` is separated then the comparison `X ×_Z Y ⟶ X ×_T Y` is a closed
immersion. -/
@[stacks 0ARQ "part (2), for Z ⟶ T separated"]
theorem isClosedImmersion_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hh : IsSeparatedMorphism B S hS h) :
    IsClosedImmersion B S hS (pullback.mapDesc f g h) :=
  isClosedImmersion_of_isPullback B S hS (isPullback_mapDesc B S hS f g h) hh

/-- If the relative diagonal of `h : Z ⟶ T` is quasi-compact then so is the comparison
`X ×_Z Y ⟶ X ×_T Y`, quasi-compactness being read as `AlgebraicGeometry.Space.IsQuasiCompactULift`
in both. -/
-- NO 0ARQ attribute: this uses this file's IsQuasiSeparatedMorphism / IsQuasiCompactULift,
-- whose quasi-compactness of the diagonal is read in the sense of algebraic spaces, a priori
-- STRONGER than the source's quasi-compactness, so the statement is not comparable to part (3)
-- term by term (stronger hypothesis, stronger conclusion). The neighbouring
-- isQuasiSeparatedMorphism_of_isPullback is deliberately left untagged for 0ARP for exactly this
-- reason; this follows that precedent.
-- Part (3) for the source's own quasi-compactness carries the tag instead, at
-- `AlgebraicGeometry.FormalSpace.isQuasiCompact_mapDesc` in
-- `StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiSeparatedMorphism`.
theorem isQuasiCompactULift_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hh : IsQuasiSeparatedMorphism B S hS h) :
    Space.IsQuasiCompactULift.{u + 1} B S hS (pullback.mapDesc f g h).hom :=
  isQuasiCompactULift_of_isPullback B S hS
    ((isPullback_mapDesc B S hS f g h).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hh

end MapDesc

end AlgebraicGeometry.FormalSpace

add_to_stacks 0ARQ "part (1): monomorphism" CategoryTheory.Limits.pullback.mono_mapDesc

end
