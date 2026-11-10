module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalRepresentableMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# The relative diagonal of a representable morphism of stacks is representable (Stacks 04YQ)

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over the big fppf site of `S` which is representable by algebraic spaces. Its
relative diagonal

`Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`

is a *representable* 1-morphism in the sense of Stacks 02Y7 — that is, representable by
**schemes**, not merely by algebraic spaces.

## Main results

* `Stack.isRepresentableMorphism_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`:
  the relative diagonal of a 1-morphism of algebraic stacks representable by algebraic spaces is
  representable by schemes.
* `CategoryTheory.exists_iso_yoneda_of_subsingleton`: a presheaf of subsingletons inhabited
  exactly where two global sections of a presheaf with representable diagonal agree is
  representable.
* `RelativeDiagonalFibre.nonempty_relVertHom_iff_fibreSection_eq`:
  the square 04XT read elementwise — the Isom presheaf is inhabited at `V` exactly where the two
  sections of the fibre of `f` named by the components of `Y` agree.

## References

* [Stacks Project, Tag 02Y7](https://stacks.math.columbia.edu/tag/02Y7)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

/-- Two subsingletons which are inhabited together are equivalent. -/
noncomputable def Equiv.ofNonemptyIff {α β : Type*} (ha : Subsingleton α) (hb : Subsingleton β)
    (h : Nonempty α ↔ Nonempty β) : α ≃ β where
  toFun a := (h.1 ⟨a⟩).some
  invFun b := (h.2 ⟨b⟩).some
  left_inv _ := ha.allEq _ _
  right_inv _ := hb.allEq _ _

namespace CategoryTheory

universe v u

section Presheaf

variable {C : Type u} [Category.{v} C]

/-- **A subsingleton-valued presheaf cut out by two sections of a presheaf with representable
diagonal is representable.** Let `T` be a final object of `C`, let `A` be a presheaf of sets on
`C` whose diagonal is representable (relative to the Yoneda embedding), and let `s₁`, `s₂` be
global sections of `A`. A presheaf `P` on `C` taking subsingleton values which is inhabited over
`V` exactly when `s₁` and `s₂` agree over `V` is represented by an object of `C`. -/
theorem exists_iso_yoneda_of_subsingleton {T : C} (hT : IsTerminal T)
    {A : Cᵒᵖ ⥤ Type v} (hA : (yoneda (C := C)).relativelyRepresentable (diag A))
    (s₁ s₂ : ∀ V : C, A.obj (op V))
    (hs₁ : ∀ {V W : C} (g : V ⟶ W), A.map g.op (s₁ W) = s₁ V)
    (hs₂ : ∀ {V W : C} (g : V ⟶ W), A.map g.op (s₂ W) = s₂ V)
    {P : Cᵒᵖ ⥤ Type v} (hsub : ∀ V, Subsingleton (P.obj V))
    (hiff : ∀ V : C, Nonempty (P.obj (op V)) ↔ s₁ V = s₂ V) :
    ∃ Z : C, Nonempty (P ≅ yoneda.obj Z) := by
  classical
  have hTerm : IsTerminal (yoneda.obj T) := hT.isTerminalObj yoneda T
  set σ₁ : yoneda.obj T ⟶ A := PresheafOfCategories.sectionHom s₁ hs₁ T with hσ₁
  set σ₂ : yoneda.obj T ⟶ A := PresheafOfCategories.sectionHom s₂ hs₂ T with hσ₂
  obtain ⟨W, w, k, hpb⟩ := hA (prod.lift σ₁ (hTerm.from (yoneda.obj T) ≫ σ₂))
  have hbig : IsPullback (yoneda.map w) (hTerm.from (yoneda.obj W)) σ₁ σ₂ :=
    IsPullback.of_diag_prodLift_isTerminal hTerm hpb
  have hmonoy : Mono (yoneda.map w) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.monomorphisms _) hbig.flip ⟨fun _ _ _ => hTerm.hom_ext _ _⟩
  have hmono : Mono w := yoneda.mono_of_mono_map hmonoy
  have hsubW : ∀ V : C, Subsingleton (V ⟶ W) :=
    fun V => ⟨fun g h => by rw [← cancel_mono w]; exact hT.hom_ext _ _⟩
  have hiffW : ∀ V : C, Nonempty (V ⟶ W) ↔ s₁ V = s₂ V := by
    intro V
    constructor
    · rintro ⟨g⟩
      simpa [hσ₁, hσ₂, PresheafOfCategories.sectionHom] using
        congrArg (fun (α : yoneda.obj W ⟶ A) => α.app (op V) g) hbig.w
    · intro heq
      have hcomm : yoneda.map (hT.from V) ≫ σ₁ = yoneda.map (hT.from V) ≫ σ₂ := by
        ext V' u
        change s₁ V'.unop = s₂ V'.unop
        rw [← hs₁ u, ← hs₂ u, heq]
      exact ⟨yonedaEquiv (hbig.lift (yoneda.map (hT.from V)) (yoneda.map (hT.from V)) hcomm)⟩
  refine ⟨W, ⟨NatIso.ofComponents
    (fun V => (Equiv.ofNonemptyIff (hsub V) (hsubW V.unop)
      ((hiff V.unop).trans (hiffW V.unop).symm)).toIso) ?_⟩⟩
  intro V V' g
  ext x
  exact (hsubW V'.unop).allEq _ _

/-- **Representability of a presheaf transports along an equivalence of sites.** If the
restriction of `P` along the forward functor of an equivalence `E : A ≌ B` is represented by `Z`,
then `P` is represented by the image of `Z`. -/
def isoYonedaOfEquivalence {A : Type*} [Category.{v} A] {B : Type*} [Category.{v} B]
    (E : A ≌ B) {P : Bᵒᵖ ⥤ Type v} {Z : A} (i : E.functor.op ⋙ P ≅ yoneda.obj Z) :
    P ≅ yoneda.obj (E.functor.obj Z) := by
  have ff := E.fullyFaithfulFunctor
  have j : E.functor.op ⋙ yoneda.obj (E.functor.obj Z) ≅ yoneda.obj Z :=
    NatIso.ofComponents (fun a => (ff.homEquiv (X := a.unop) (Y := Z)).symm.toIso) (by
      intro a b g
      ext h
      apply E.functor.map_injective
      simp [Functor.FullyFaithful.homEquiv])
  exact (E.op.invFunIdAssoc P).symm ≪≫
    Functor.isoWhiskerLeft E.op.inverse (i ≪≫ j.symm) ≪≫ E.op.invFunIdAssoc _

end Presheaf

namespace TwoFibreProductOver.RelativeDiagonalFibre

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ a

attribute [local implicit_reducible] TwoFibreProductOver.lift TwoFibreProductOver.fst
  TwoFibreProductOver.snd

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {p : X ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}

/-- The common `𝒴`-point of a point of `X ×_𝒴 X` over `𝒯` is a 1-morphism over `𝒞`. -/
theorem h1F' (p𝒯 : 𝒯 ⥤ 𝒞) {Y : 𝒯 ⥤ RelProd p q F} (hF : F ⋙ q = p)
    (hY : Y ⋙ RelProdP p q F = p𝒯) : (Y₁' Y ⋙ F) ⋙ q = p𝒯 := by
  rw [Functor.assoc, hF]; exact h1' hY

/-- The comparison isomorphism of a point of `X ×_𝒴 X` over `𝒯`, read as a 2-cell between the
images under `F` of its two components. -/
def relCompIso (Y : 𝒯 ⥤ RelProd p q F) : Y₁' Y ⋙ F ≅ Y₂' Y ⋙ F :=
  NatIso.ofComponents (fun a => (Y.obj a).iso) (fun {_ _} h => iso_naturality h)

/-- The projection to `𝒯` of the fibre `𝒯 ×_{F Y₁, 𝒴, F} X` of `F` over the common `𝒴`-point of
a point `Y` of `X ×_𝒴 X` over `𝒯`. -/
abbrev fibreFst (p𝒯 : 𝒯 ⥤ 𝒞) (Y : 𝒯 ⥤ RelProd p q F) :
    TwoFibreProductOver p𝒯 p q (Y₁' Y ⋙ F) F ⥤ 𝒯 :=
  TwoFibreProductOver.fst p𝒯 p q (Y₁' Y ⋙ F) F

variable (p𝒯 : 𝒯 ⥤ 𝒞) {Y : 𝒯 ⥤ RelProd p q F}

/-- **The first component of `Y` as a section of the fibre of `F`.** It sends `a` to the first
component of `Y a` together with the identity identification of its image under `F` with the
common `𝒴`-point. -/
def fibreSec₁ (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯) :
    𝒯 ⥤ TwoFibreProductOver p𝒯 p q (Y₁' Y ⋙ F) F :=
  TwoFibreProductOver.lift p𝒯 p q (Y₁' Y ⋙ F) F p𝒯 (𝟭 𝒯) (Y₁' Y)
    (Functor.id_comp p𝒯) (h1' hY) (Iso.refl _)
    (fun w => IsHomLift.id (Functor.congr_obj (h1F' p𝒯 hF hY) w))

/-- **The second component of `Y` as a section of the fibre of `F`.** It sends `a` to the second
component of `Y a` together with the comparison isomorphism of `Y` at `a`. -/
def fibreSec₂ (_hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯) :
    𝒯 ⥤ TwoFibreProductOver p𝒯 p q (Y₁' Y ⋙ F) F :=
  TwoFibreProductOver.lift p𝒯 p q (Y₁' Y ⋙ F) F p𝒯 (𝟭 𝒯) (Y₂' Y)
    (Functor.id_comp p𝒯) (h2' hY) (relCompIso Y)
    (fun w => isHomLift_vertical_iso hY w)

variable {p𝒯}

/-- The first section lies over `𝒯`: it sends `g` to a morphism of the fibre over `g`. -/
lemma isHomLift_fibreSec₁_map (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯)
    {a b : 𝒯} (g : a ⟶ b) :
    (fibreFst p𝒯 Y).IsHomLift g ((fibreSec₁ p𝒯 hF hY).map g) :=
  IsHomLift.map (fibreFst p𝒯 Y) ((fibreSec₁ p𝒯 hF hY).map g)

/-- The second section lies over `𝒯`: it sends `g` to a morphism of the fibre over `g`. -/
lemma isHomLift_fibreSec₂_map (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯)
    {a b : 𝒯} (g : a ⟶ b) :
    (fibreFst p𝒯 Y).IsHomLift g ((fibreSec₂ p𝒯 hF hY).map g) :=
  IsHomLift.map (fibreFst p𝒯 Y) ((fibreSec₂ p𝒯 hF hY).map g)

/-- **A vertical morphism over the comparison isomorphism is a vertical morphism of the fibre of
`F` between the two sections.** The `X`-component is the given morphism and the `𝒯`-component is
the identity. -/
def homOfRelVertHom (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯) (a : 𝒯)
    (m : RelVertHom p𝒯 Y a) : (fibreSec₁ p𝒯 hF hY).obj a ⟶ (fibreSec₂ p𝒯 hF hY).obj a where
  hbase := 𝟙 (p𝒯.obj a)
  a := 𝟙 a
  b := m.1.1
  ha := IsHomLift.id rfl
  hb := m.1.2
  w := (congrArg (fun k => k ≫ (Y.obj a).iso.hom) ((Y₁' Y ⋙ F).map_id a)).trans
    ((Category.id_comp _).trans (m.2.symm.trans (Category.id_comp (F.map m.1.1)).symm))

/-- `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.homOfRelVertHom` is vertical. -/
lemma isHomLift_homOfRelVertHom (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯) (a : 𝒯)
    (m : RelVertHom p𝒯 Y a) :
    (fibreFst p𝒯 Y).IsHomLift (𝟙 a) (homOfRelVertHom hF hY a m) :=
  IsHomLift.map (fibreFst p𝒯 Y) (homOfRelVertHom hF hY a m)

/-- **The converse: the `X`-component of a vertical morphism of the fibre of `F` between the two
sections is a vertical morphism over the comparison isomorphism.** -/
def relVertHomOfHom (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯) (a : 𝒯)
    (u : (fibreSec₁ p𝒯 hF hY).obj a ⟶ (fibreSec₂ p𝒯 hF hY).obj a)
    (hu : (fibreFst p𝒯 Y).IsHomLift (𝟙 a) u) : RelVertHom p𝒯 Y a := by
  have ha : u.a = 𝟙 a :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (fibreFst p𝒯 Y) ((fibreSec₁ p𝒯 hF hY).obj a)
      ((fibreSec₂ p𝒯 hF hY).obj a) (𝟙 a) u hu).symm
  have hmap : p𝒯.map u.a = 𝟙 (p𝒯.obj a) :=
    (congrArg (fun k => p𝒯.map k) ha).trans (p𝒯.map_id a)
  have hbase : u.hbase = 𝟙 (p𝒯.obj a) :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ p𝒯 ((fibreSec₁ p𝒯 hF hY).obj a).x
      ((fibreSec₂ p𝒯 hF hY).obj a).x u.hbase u.a u.ha).trans hmap
  refine ⟨⟨u.b, ?_⟩, ?_⟩
  · exact hbase ▸ u.hb
  · have hid : (Y₁' Y ⋙ F).map u.a = 𝟙 ((Y₁' Y ⋙ F).obj a) :=
      (congrArg (fun k => (Y₁' Y ⋙ F).map k) ha).trans ((Y₁' Y ⋙ F).map_id a)
    have hw : (Y₁' Y ⋙ F).map u.a ≫ (Y.obj a).iso.hom
        = 𝟙 ((Y₁' Y ⋙ F).obj a) ≫ F.map u.b := u.w
    have h3 : 𝟙 ((Y₁' Y ⋙ F).obj a) ≫ (Y.obj a).iso.hom
        = 𝟙 ((Y₁' Y ⋙ F).obj a) ≫ F.map u.b :=
      (congrArg (fun k => k ≫ (Y.obj a).iso.hom) hid).symm.trans hw
    exact ((Category.id_comp (F.map u.b)).symm.trans h3.symm).trans (Category.id_comp _)

section Sections

variable {A : 𝒯ᵒᵖ ⥤ Type a}

/-- The section of `A` named by the first component of `Y`, for `A` a presheaf whose category of
elements is equivalent over `𝒯` to the fibre of `F` over the common `𝒴`-point of `Y`. -/
def fibreSection₁ (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (e : StacksRepresentableCFG.EquivalenceOver (fibreFst p𝒯 Y)
      (presheafOfCategories (A ⋙ typeToCat)).p) (V : 𝒯) : A.obj (op V) :=
  PresheafOfCategories.sectionOfObj e ((fibreSec₁ p𝒯 hF hY).obj V) rfl

/-- The section of `A` named by the second component of `Y`. -/
def fibreSection₂ (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (e : StacksRepresentableCFG.EquivalenceOver (fibreFst p𝒯 Y)
      (presheafOfCategories (A ⋙ typeToCat)).p) (V : 𝒯) : A.obj (op V) :=
  PresheafOfCategories.sectionOfObj e ((fibreSec₂ p𝒯 hF hY).obj V) rfl

/-- The section named by a family of objects lying over the identity of `𝒯` and lifting
the morphisms of `𝒯` is compatible with restriction. -/
private theorem map_sectionOfObj_of_isHomLift
    (e : StacksRepresentableCFG.EquivalenceOver (fibreFst p𝒯 Y)
      (presheafOfCategories (A ⋙ typeToCat)).p)
    (s : 𝒯 ⥤ TwoFibreProductOver p𝒯 p q (Y₁' Y ⋙ F) F)
    (hobj : ∀ V, (fibreFst p𝒯 Y).obj (s.obj V) = V)
    (hs : ∀ {a b : 𝒯} (g : a ⟶ b), (fibreFst p𝒯 Y).IsHomLift g (s.map g))
    {V₁ V₂ : 𝒯} (g : V₁ ⟶ V₂) :
    A.map g.op (PresheafOfCategories.sectionOfObj e (s.obj V₂) (hobj V₂)) =
      PresheafOfCategories.sectionOfObj e (s.obj V₁) (hobj V₁) :=
  (PresheafOfCategories.sectionOfObj_map e _ _ g (s.map g) (hs g)).symm

/-- The family of `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.fibreSection₁` is a
global section of `A`: it is compatible with restriction. -/
lemma fibreSection₁_map (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (e : StacksRepresentableCFG.EquivalenceOver (fibreFst p𝒯 Y)
      (presheafOfCategories (A ⋙ typeToCat)).p) {V₁ V₂ : 𝒯} (g : V₁ ⟶ V₂) :
    A.map g.op (fibreSection₁ hF hY e V₂) = fibreSection₁ hF hY e V₁ :=
  map_sectionOfObj_of_isHomLift e _ (fun _ => rfl) (isHomLift_fibreSec₁_map hF hY) g

/-- The family of `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.fibreSection₂` is a
global section of `A`. -/
lemma fibreSection₂_map (hF : F ⋙ q = p) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (e : StacksRepresentableCFG.EquivalenceOver (fibreFst p𝒯 Y)
      (presheafOfCategories (A ⋙ typeToCat)).p) {V₁ V₂ : 𝒯} (g : V₁ ⟶ V₂) :
    A.map g.op (fibreSection₂ hF hY e V₂) = fibreSection₂ hF hY e V₁ :=
  map_sectionOfObj_of_isHomLift e _ (fun _ => rfl) (isHomLift_fibreSec₂_map hF hY) g

/-- **The square 04XT, read elementwise.** A vertical morphism between the two components of `Y`
over `V` lying over the comparison isomorphism of `Y` exists exactly when the two sections of `A`
named by those components agree over `V`. -/
theorem nonempty_relVertHom_iff_fibreSection_eq (hF : F ⋙ q = p)
    (hY : Y ⋙ RelProdP p q F = p𝒯)
    (e : StacksRepresentableCFG.EquivalenceOver (fibreFst p𝒯 Y)
      (presheafOfCategories (A ⋙ typeToCat)).p) (V : 𝒯) :
    Nonempty (RelVertHom p𝒯 Y V) ↔ fibreSection₁ hF hY e V = fibreSection₂ hF hY e V := by
  constructor
  · rintro ⟨m⟩
    exact PresheafOfCategories.sectionOfObj_eq_of_hom e (z := (fibreSec₁ p𝒯 hF hY).obj V)
      (z' := (fibreSec₂ p𝒯 hF hY).obj V) (W := V) rfl rfl
      (homOfRelVertHom hF hY V m) (isHomLift_homOfRelVertHom hF hY V m)
  · intro heq
    have i := PresheafOfCategories.fiberIsoOfSectionOfObj_eq e
      (z := (fibreSec₁ p𝒯 hF hY).obj V) (z' := (fibreSec₂ p𝒯 hF hY).obj V) (W := V) rfl rfl heq
    exact ⟨relVertHomOfHom hF hY V (Functor.Fiber.fiberInclusion.map i.hom) i.hom.2⟩

end Sections

end TwoFibreProductOver.RelativeDiagonalFibre

end CategoryTheory

namespace AlgebraicGeometry.Stack

open CategoryTheory.TwoFibreProductOver
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

universe u t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` of a 1-morphism `f` of algebraic stacks
over the big fppf site of `S` which is representable by algebraic spaces is a *representable*
1-morphism in the sense of Stacks 02Y7 — representable by objects of the site, that is by
schemes. -/
@[stacks 04YQ "part (1): representable by schemes"]
theorem isRepresentableMorphism_relativeDiagonal_of_isRepresentableByAlgebraicSpaces
    {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p
      (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p
      (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor := by
  have hp := 𝒳.val.isFiberedInGroupoids
  have hq := 𝒴.val.isFiberedInGroupoids
  have hfib : 𝒴.val.val.p.IsFibered := hq.isFibered
  have hfaith := ((AlgebraicGeometry.isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS f.hom
    𝒴.val.val.p.chosenPullbacks).1 hf).1
  refine
    Stacks.RepresentableMorphism.isRepresentableMorphism_relativeDiagonal_of_forall_representable
    hq hp f.hom.hom.w ?_
  intro U Y hY
  have hY' : (U.iteratedSliceBackward ⋙ Y) ⋙
      RelProdP 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor = Over.map U.hom := by
    rw [Functor.assoc, hY]; exact Over.iteratedSliceBackward_forget U
  obtain ⟨A, hA, ⟨e⟩⟩ := hf U (Y₁' (U.iteratedSliceBackward ⋙ Y) ⋙ f.hom.hom.toFunctor)
    (h1F' _ f.hom.hom.w hY')
  obtain ⟨W, ⟨iso⟩⟩ := CategoryTheory.exists_iso_yoneda_of_subsingleton
    (T := Over.mk (𝟙 U.left)) Over.mkIdTerminal hA.diagonal_representable
    (fibreSection₁ f.hom.hom.w hY' e) (fibreSection₂ f.hom.hom.w hY' e)
    (fun g => fibreSection₁_map f.hom.hom.w hY' e g)
    (fun g => fibreSection₂_map f.hom.hom.w hY' e g)
    (P := relVertHomPresheaf hq hp hY' f.hom.hom.w)
    (fun V => subsingleton_relVertHom_of_faithful f.hom.hom.w V.unop (hfaith _))
    (fun V => nonempty_relVertHom_iff_fibreSection_eq f.hom.hom.w hY' e V)
  refine ⟨U.iteratedSliceBackward.obj W, ⟨Functor.isoWhiskerRight ?_ uliftFunctor⟩⟩
  exact CategoryTheory.isoYonedaOfEquivalence (Over.iteratedSliceEquiv U).symm iso

end AlgebraicGeometry.Stack

end
