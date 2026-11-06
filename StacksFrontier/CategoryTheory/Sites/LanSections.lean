module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Sections of a left Kan extension along a functor of sites

Let `u : C ⥤ D` be a functor and `F` a presheaf of sets on `C`. The left Kan extension
`u_p F` of `F` along `u.op` has, over an object `Y` of `D`, the colimit of `F(U)` over the arrows
`Y ⟶ u(U)`. Its sections are therefore represented by pairs `(φ, t)` of an arrow
`φ : Y ⟶ u(U)` and a section `t` of `F` over `U`; the section so represented is the pullback
along `φ` of the image of `t` under the unit `F(U) ⟶ (u_p F)(u(U))`.

When the index categories of these colimits are filtered (for instance when `u` is
representably flat), two sections represented by the same arrow agree exactly when the
representing sections of `F` agree after restriction along some factorization of the arrow.

Combined with a locally injective and locally surjective map `u_p F ⟶ P` to a presheaf `P`
(for instance the unit of sheafification), these give the local description of the sections of
`P` used to compute inverse images along morphisms of sites.

## Main definitions

* `CategoryTheory.Functor.lanSection`: the section of `u_p F` over `Y` represented by an arrow
  `φ : Y ⟶ u(U)` and a section of `F` over `U`.

## Main results

* `CategoryTheory.Functor.lanSection_map`, `CategoryTheory.Functor.lanSection_comp_map`: the
  behaviour of represented sections under restriction and under change of representative.
* `CategoryTheory.Functor.exists_lanSection_eq`: every section of `u_p F` is represented.
* `CategoryTheory.Functor.exists_lanSection_eq₂`: two sections over the same object are
  represented by a common arrow, when the index category is filtered.
* `CategoryTheory.Functor.exists_lanSection_eq_of_lanSection_eq`: two sections represented by
  the same arrow agree if and only if the representing sections agree after restriction along a
  factorization of the arrow, when the index category is filtered.
* `CategoryTheory.Functor.exists_covering_lanSection₂` and
  `CategoryTheory.Functor.exists_covering_of_lanSection_eq`: the local versions for a locally
  bijective map out of `u_p F`.

## References

* [Stacks Project, Tag 00VC](https://stacks.math.columbia.edu/tag/00VC)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
  [∀ G : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension G] (F : Cᵒᵖ ⥤ Type w)

/-- The section of the left Kan extension of `F` along `u.op` over `Y` represented by an arrow
`φ : Y ⟶ u.obj U` and a section `t` of `F` over `U`: the image of `t` under the unit of the
extension, pulled back along `φ`. -/
def lanSection {Y : D} {U : C} (φ : Y ⟶ u.obj U) (t : F.obj (op U)) :
    (u.op.lan.obj F).obj (op Y) :=
  (u.op.lan.obj F).map φ.op ((u.op.lanUnit.app F).app (op U) t)

/-- Restricting a represented section along `h` composes the representing arrow with `h`. -/
@[simp]
lemma lanSection_map {Y Z : D} {U : C} (h : Z ⟶ Y) (φ : Y ⟶ u.obj U) (t : F.obj (op U)) :
    (u.op.lan.obj F).map h.op (u.lanSection F φ t) = u.lanSection F (h ≫ φ) t := by
  simp [lanSection]

/-- A representing arrow which factors through `u.map a` may be replaced by the factor, at the
cost of restricting the representing section along `a`. -/
lemma lanSection_comp_map {Y : D} {U U' : C} (φ : Y ⟶ u.obj U) (a : U ⟶ U')
    (t : F.obj (op U')) :
    u.lanSection F (φ ≫ u.map a) t = u.lanSection F φ (F.map a.op t) := by
  have h := NatTrans.naturality_apply (u.op.lanUnit.app F) a.op t
  dsimp at h
  simp only [lanSection, op_comp, Functor.map_comp_apply, h]

variable [u.op.HasPointwiseLeftKanExtension F]

/-- The value of the left Kan extension at `op Y` is the colimit of the cocone whose legs are
the represented sections. -/
private noncomputable def lanCoconeIsColimit (Y : D) :
    IsColimit ((LeftExtension.mk _ (u.op.lanUnit.app F)).coconeAt (op Y)) :=
  isPointwiseLeftKanExtensionLeftKanExtensionUnit u.op F (op Y)

omit [u.op.HasPointwiseLeftKanExtension F] in
private lemma lanCocone_ι_app {Y : D} (g : CostructuredArrow u.op (op Y))
    (t : F.obj g.left) :
    ((LeftExtension.mk _ (u.op.lanUnit.app F)).coconeAt (op Y)).ι.app g t =
      u.lanSection F g.hom.unop t := rfl

/-- Every section of the left Kan extension is represented by an arrow and a section of `F`. -/
lemma exists_lanSection_eq {Y : D} (q : (u.op.lan.obj F).obj (op Y)) :
    ∃ (U : C) (φ : Y ⟶ u.obj U) (t : F.obj (op U)), u.lanSection F φ t = q := by
  obtain ⟨g, t, rfl⟩ := Types.jointly_surjective_of_isColimit (lanCoconeIsColimit u F Y) q
  exact ⟨g.left.unop, g.hom.unop, t, rfl⟩

/-- Two sections of the left Kan extension over `Y` are represented by a common arrow, when the
index category of the colimit at `Y` is filtered. -/
lemma exists_lanSection_eq₂ {Y : D} [IsFiltered (CostructuredArrow u.op (op Y))]
    (q₁ q₂ : (u.op.lan.obj F).obj (op Y)) :
    ∃ (U : C) (φ : Y ⟶ u.obj U) (t₁ t₂ : F.obj (op U)),
      u.lanSection F φ t₁ = q₁ ∧ u.lanSection F φ t₂ = q₂ := by
  obtain ⟨g, t₁, t₂, h₁, h₂⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ (lanCoconeIsColimit u F Y) q₁ q₂
  exact ⟨g.left.unop, g.hom.unop, t₁, t₂, h₁, h₂⟩

/-- Two sections represented by the same arrow `φ` agree only if the representing sections agree
after restriction along a factorization `φ = ψ ≫ u.map a`, when the index category of the
colimit is filtered. -/
lemma exists_lanSection_eq_of_lanSection_eq {Y : D}
    [IsFiltered (CostructuredArrow u.op (op Y))] {U : C} (φ : Y ⟶ u.obj U)
    (t t' : F.obj (op U)) (h : u.lanSection F φ t = u.lanSection F φ t') :
    ∃ (U' : C) (ψ : Y ⟶ u.obj U') (a : U' ⟶ U),
      ψ ≫ u.map a = φ ∧ F.map a.op t = F.map a.op t' := by
  let g : CostructuredArrow u.op (op Y) := CostructuredArrow.mk φ.op
  replace h : ((LeftExtension.mk _ (u.op.lanUnit.app F)).coconeAt (op Y)).ι.app g t =
      ((LeftExtension.mk _ (u.op.lanUnit.app F)).coconeAt (op Y)).ι.app g t' := h
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (lanCoconeIsColimit u F Y) (i := g) t t').1 h
  refine ⟨j.left.unop, j.hom.unop, f.left.unop, ?_, hf⟩
  have hw := CostructuredArrow.w f
  apply Quiver.Hom.op_inj
  simpa [g] using hw

section Sheaf

variable (K : GrothendieckTopology D) {P : Dᵒᵖ ⥤ Type w} (η : u.op.lan.obj F ⟶ P)

/-- **Local representation of two sections.** For a locally surjective map `η` out of the left
Kan extension, two sections of the target over `Y` are, on a covering sieve of `Y`, the images
of sections represented by a common arrow. -/
lemma exists_covering_lanSection₂ [Presheaf.IsLocallySurjective K η]
    [∀ Y : D, IsFiltered (CostructuredArrow u.op (op Y))] {Y : D} (s₁ s₂ : P.obj (op Y)) :
    ∃ R ∈ K Y, ∀ ⦃Z : D⦄ (h : Z ⟶ Y), R h →
      ∃ (U : C) (φ : Z ⟶ u.obj U) (t₁ t₂ : F.obj (op U)),
        P.map h.op s₁ = η.app _ (u.lanSection F φ t₁) ∧
          P.map h.op s₂ = η.app _ (u.lanSection F φ t₂) := by
  refine ⟨Presheaf.imageSieve η s₁ ⊓ Presheaf.imageSieve η s₂,
    K.intersection_covering (Presheaf.imageSieve_mem K η s₁)
      (Presheaf.imageSieve_mem K η s₂), ?_⟩
  rintro Z h ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩
  obtain ⟨U, φ, t₁, t₂, rfl, rfl⟩ := u.exists_lanSection_eq₂ F q₁ q₂
  exact ⟨U, φ, t₁, t₂, hq₁.symm, hq₂.symm⟩

/-- **Local representation of one section.** For a locally surjective map `η` out of the left
Kan extension, a section of the target over `Y` is, on a covering sieve of `Y`, the image of a
represented section. -/
lemma exists_covering_lanSection [Presheaf.IsLocallySurjective K η] {Y : D}
    (s : P.obj (op Y)) :
    ∃ R ∈ K Y, ∀ ⦃Z : D⦄ (h : Z ⟶ Y), R h →
      ∃ (U : C) (φ : Z ⟶ u.obj U) (t : F.obj (op U)),
        P.map h.op s = η.app _ (u.lanSection F φ t) := by
  refine ⟨Presheaf.imageSieve η s, Presheaf.imageSieve_mem K η s, ?_⟩
  rintro Z h ⟨q, hq⟩
  obtain ⟨U, φ, t, rfl⟩ := u.exists_lanSection_eq F q
  exact ⟨U, φ, t, hq.symm⟩

/-- **Local agreement of represented sections.** For a locally injective map `η` out of the left
Kan extension, if two sections represented by the same arrow `φ` have the same image, then on a
covering sieve the arrow factors as `ψ ≫ u.map a` with the representing sections agreeing after
restriction along `a`. -/
lemma exists_covering_of_lanSection_eq [Presheaf.IsLocallyInjective K η]
    [∀ Y : D, IsFiltered (CostructuredArrow u.op (op Y))] {Y : D} {U : C}
    (φ : Y ⟶ u.obj U) (t t' : F.obj (op U))
    (h : η.app _ (u.lanSection F φ t) = η.app _ (u.lanSection F φ t')) :
    ∃ R ∈ K Y, ∀ ⦃Z : D⦄ (g : Z ⟶ Y), R g →
      ∃ (U' : C) (ψ : Z ⟶ u.obj U') (a : U' ⟶ U),
        ψ ≫ u.map a = g ≫ φ ∧ F.map a.op t = F.map a.op t' := by
  refine ⟨_, Presheaf.equalizerSieve_mem K η _ _ h, ?_⟩
  intro Z g hg
  simp only [Presheaf.equalizerSieve_apply, lanSection_map] at hg
  exact u.exists_lanSection_eq_of_lanSection_eq F (g ≫ φ) t t' hg

end Sheaf

end CategoryTheory.Functor

end
