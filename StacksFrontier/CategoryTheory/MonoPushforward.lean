module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pushing a presheaf forward along a monomorphism

Let `i : F₀ ⟶ F` be a morphism of presheaves of types and `u₀ : C₀ ⟶ F₀` a presheaf over `F₀`.
The *pushforward* of `u₀` along `i` is the presheaf over `F` whose sections over `T` are a
section `x` of `F` over `T` together with a lift of the base change of `x` along `i` to `C₀`:
for every `g : T' ⟶ T` at which `x` restricts into `F₀`, a section of `C₀` over `T'` lying over
that restriction, compatibly in `g`. It is the value at `u₀` of the right adjoint of pullback
along `i` on presheaves over `F` and over `F₀`; only the object and the unit square are built
here.

When `i` is a monomorphism the base change of the pushforward along `i` is `C₀` again:
`CategoryTheory.isPullback_monoPushforward_unit`. This is the form in which a morphism étale
over the thin space of a thickening is extended to the ambient space (Stacks 05ZH).

## Main definitions

* `CategoryTheory.MonoPushforwardSection`: a section of the pushforward.
* `CategoryTheory.monoPushforward`: the pushforward presheaf, with its projection
  `CategoryTheory.monoPushforward.π` to `F` and its unit `CategoryTheory.monoPushforward.unit`.

## Main results

* `CategoryTheory.isPullback_monoPushforward_unit`: for a monomorphism `i`, the unit square
  exhibits `C₀` as the base change of the pushforward along `i`.
* `CategoryTheory.monoPushforward.isPullback_map`: pushing forward along `i` and along `i ≫ e`,
  for a monomorphism `e`, gives a cartesian square over `e`.
* `CategoryTheory.monoPushforwardDiagram`: for a diagram `P` of presheaves with monomorphic
  transitions over a preorder with a least element `o`, the pushforwards of one `u₀` over `P o`
  along the transitions out of `o`, as a diagram over `P`; it is equifibered
  (`CategoryTheory.monoPushforwardDiagram_equifibered`). This is how an étale chart of one stage
  of a system of thickenings is transported to all later stages (Stacks 0AIU).

## Implementation notes

A section records its lift as an `Option`-valued function of `g : T' ⟶ T`, defined at `g`
exactly when the restriction of `x` along `g` lies in the image of `i`. This keeps the type of
a section independent of `x`, so that restriction of sections and the functor laws are plain
equalities of structures; the alternative of a morphism out of the pullback of `x` along `i`
makes the type of the lift depend on `x`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v

namespace CategoryTheory

variable {C : Type w} [Category.{v} C] {F₀ F C₀ : Cᵒᵖ ⥤ Type (max w v)}
  (i : F₀ ⟶ F) (u₀ : C₀ ⟶ F₀)

/-- A section over `T` of the pushforward of `u₀ : C₀ ⟶ F₀` along `i : F₀ ⟶ F`: a section
`base` of `F` over `T`, and for every `g : T' ⟶ T` at which `base` restricts into the image of
`i` a section of `C₀` over `T'` lying over that restriction, compatible with restriction along
any `h : T'' ⟶ T'`. The arrows at which the lift is defined form a sieve, not a cosieve, so
compatibility is asked only where the lift is defined. -/
@[ext]
structure MonoPushforwardSection (T : C) where
  /-- The underlying section of `F`. -/
  base : F.obj (op T)
  /-- The lift, defined exactly at the arrows along which `base` restricts into `F₀`. -/
  sect : ∀ ⦃T' : C⦄ (_ : T' ⟶ T), Option (C₀.obj (op T'))
  isSome_sect_iff : ∀ ⦃T' : C⦄ (g : T' ⟶ T),
    (sect g).isSome ↔ F.map g.op base ∈ Set.range (i.app (op T'))
  sect_over : ∀ ⦃T' : C⦄ (g : T' ⟶ T) (a : C₀.obj (op T')),
    sect g = some a → i.app (op T') (u₀.app (op T') a) = F.map g.op base
  sect_comp : ∀ ⦃T' T'' : C⦄ (g : T' ⟶ T) (h : T'' ⟶ T') (a : C₀.obj (op T')),
    sect g = some a → sect (h ≫ g) = some (C₀.map h.op a)

namespace MonoPushforwardSection

variable {i u₀}

/-- Restriction of a section of the pushforward along `k : T₁ ⟶ T`. -/
def restrict {T T₁ : C} (s : MonoPushforwardSection i u₀ T) (k : T₁ ⟶ T) :
    MonoPushforwardSection i u₀ T₁ where
  base := F.map k.op s.base
  sect _ g := s.sect (g ≫ k)
  isSome_sect_iff _ g := by
    rw [s.isSome_sect_iff, op_comp, Functor.map_comp_apply]
  sect_over _ g a h := by
    rw [s.sect_over _ a h, op_comp, Functor.map_comp_apply]
  sect_comp _ _ g h a ha := by
    rw [Category.assoc]
    exact s.sect_comp _ h a ha

/-- The underlying section of `s.restrict k` is the restriction of that of `s` along `k`. -/
@[simp]
lemma restrict_base {T T₁ : C} (s : MonoPushforwardSection i u₀ T) (k : T₁ ⟶ T) :
    (s.restrict k).base = F.map k.op s.base := rfl

/-- The lift of `s.restrict k` at `g` is the lift of `s` at `g ≫ k`. -/
@[simp]
lemma restrict_sect {T T₁ : C} (s : MonoPushforwardSection i u₀ T) (k : T₁ ⟶ T) {T' : C}
    (g : T' ⟶ T₁) : (s.restrict k).sect g = s.sect (g ≫ k) := rfl

end MonoPushforwardSection

/-- The pushforward of `u₀ : C₀ ⟶ F₀` along `i : F₀ ⟶ F`, as a presheaf. -/
def monoPushforward : Cᵒᵖ ⥤ Type (max w v) where
  obj T := MonoPushforwardSection i u₀ T.unop
  map k := ↾fun s ↦ s.restrict k.unop
  map_id T := by
    ext s <;> simp
  map_comp k k' := by
    ext s <;> simp

/-- The sections of `monoPushforward i u₀` over `T` are the `MonoPushforwardSection`s over `T`. -/
@[simp]
lemma monoPushforward_obj (T : Cᵒᵖ) :
    (monoPushforward i u₀).obj T = MonoPushforwardSection i u₀ T.unop := rfl

/-- The pushforward acts on a section by `MonoPushforwardSection.restrict`. -/
@[simp]
lemma monoPushforward_map_apply {T T₁ : Cᵒᵖ} (k : T ⟶ T₁)
    (s : MonoPushforwardSection i u₀ T.unop) :
    (monoPushforward i u₀).map k s = s.restrict k.unop := rfl

namespace monoPushforward

/-- The projection of the pushforward to `F`. -/
def π : monoPushforward i u₀ ⟶ F where
  app _ := ↾fun s ↦ s.base
  naturality _ _ _ := rfl

/-- The section of the pushforward given by a section `a` of `C₀`: the image of `u₀ a` in
`F`, with the restrictions of `a` as its lift. -/
def unitSection {T : C} (a : C₀.obj (op T)) : MonoPushforwardSection i u₀ T where
  base := i.app (op T) (u₀.app (op T) a)
  sect _ g := some (C₀.map g.op a)
  isSome_sect_iff _ g := by
    simp only [Option.isSome_some, true_iff]
    exact ⟨u₀.app _ (C₀.map g.op a), by rw [NatTrans.naturality_apply, NatTrans.naturality_apply]⟩
  sect_over _ g b h := by
    cases h
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
  sect_comp _ _ g h b hb := by
    cases hb
    simp [op_comp]

/-- The unit of the pushforward, `CategoryTheory.monoPushforward.unitSection` on sections. -/
def unit : C₀ ⟶ monoPushforward i u₀ where
  app T := ↾fun a ↦ unitSection i u₀ (T := T.unop) a
  naturality T T₁ k := by
    ext a
    change unitSection i u₀ (C₀.map k a) = (unitSection i u₀ a).restrict k.unop
    ext
    · simp [unitSection, NatTrans.naturality_apply]
    · simp [unitSection, op_comp]

/-- The unit sends a section `a` of `C₀` to `unitSection i u₀ a`. -/
@[simp]
lemma unit_app_apply (T : Cᵒᵖ) (a : C₀.obj T) :
    (unit i u₀).app T a = unitSection i u₀ (T := T.unop) a := rfl

/-- The projection sends a section of the pushforward to its underlying section of `F`. -/
@[simp]
lemma π_app_apply (T : Cᵒᵖ) (s : MonoPushforwardSection i u₀ T.unop) :
    (π i u₀).app T s = s.base := rfl

/-- The unit followed by the projection to `F` is `u₀ ≫ i`. -/
lemma unit_π : unit i u₀ ≫ π i u₀ = u₀ ≫ i := by
  ext T a
  rfl

end monoPushforward

/-- The components of a monomorphism of presheaves of types are injective. -/
private theorem injective_app_of_mono {G G' : Cᵒᵖ ⥤ Type (max w v)} (e : G ⟶ G') [Mono e]
    (T : Cᵒᵖ) : Function.Injective (e.app T) :=
  (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app e).1 inferInstance T)

/-- **The base change of the pushforward along a monomorphism.** If `i : F₀ ⟶ F` is a
monomorphism of presheaves, the square formed by the unit `C₀ ⟶ i_* C₀`, the projection
`i_* C₀ ⟶ F`, `u₀` and `i` is cartesian: the base change of the pushforward along `i` is the
presheaf one started from. -/
theorem isPullback_monoPushforward_unit [Mono i] :
    IsPullback (monoPushforward.unit i u₀) u₀ (monoPushforward.π i u₀) i := by
  refine IsPullback.of_forall_isPullback_app fun T ↦ ?_
  have hinj := injective_app_of_mono i T
  rw [Types.isPullback_iff]
  refine ⟨by rw [← NatTrans.comp_app, ← NatTrans.comp_app, monoPushforward.unit_π], ?_, ?_⟩
  · rintro a b ⟨hab, -⟩
    have h : (monoPushforward.unitSection i u₀ a).sect (𝟙 T.unop) =
        (monoPushforward.unitSection i u₀ b).sect (𝟙 T.unop) :=
      congrArg (fun s : MonoPushforwardSection i u₀ T.unop ↦ s.sect (𝟙 T.unop)) hab
    simpa [monoPushforward.unitSection] using h
  · intro s b hsb
    change s.base = i.app T b at hsb
    have hsome : (s.sect (𝟙 T.unop)).isSome := by
      rw [s.isSome_sect_iff]
      exact ⟨b, by simpa using hsb.symm⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hsome
    have hover := s.sect_over _ a ha
    simp only [op_id, Functor.map_id_apply] at hover
    refine ⟨a, ?_, ?_⟩
    · show monoPushforward.unitSection i u₀ a = s
      refine MonoPushforwardSection.ext hover ?_
      funext T' g
      have h := s.sect_comp (𝟙 T.unop) g a ha
      rw [Category.comp_id] at h
      simp [monoPushforward.unitSection, h]
    · apply hinj
      show i.app T (u₀.app T a) = i.app T b
      rw [hover, hsb]

namespace monoPushforward

variable {i u₀} {F' : Cᵒᵖ ⥤ Type (max w v)} {i' : F₀ ⟶ F'} (e : F ⟶ F') [Mono e]

include e in
/-- Along a monomorphism `e` with `i ≫ e = i'`, a section of `F` restricts into the image of `i`
exactly when its image in `F'` restricts into the image of `i'`. -/
lemma mem_range_app_iff_of_mono (h : i ≫ e = i') (T : Cᵒᵖ) (x : F.obj T) :
    e.app T x ∈ Set.range (i'.app T) ↔ x ∈ Set.range (i.app T) := by
  have hinj := injective_app_of_mono e T
  subst h
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hinj hb⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩

/-- The section of the pushforward along `i'` given by a section of the pushforward along `i`,
for `i ≫ e = i'` with `e` a monomorphism: the image of the underlying section in `F'`, with the
same lift. -/
def mapSection (h : i ≫ e = i') {T : C} (s : MonoPushforwardSection i u₀ T) :
    MonoPushforwardSection i' u₀ T where
  base := e.app (op T) s.base
  sect := s.sect
  isSome_sect_iff T' g := by
    rw [s.isSome_sect_iff, ← NatTrans.naturality_apply e g.op s.base,
      mem_range_app_iff_of_mono e h]
  sect_over T' g a ha := by
    rw [← NatTrans.naturality_apply e g.op s.base, ← s.sect_over g a ha, ← h]
    rfl
  sect_comp := s.sect_comp

/-- The morphism from the pushforward along `i` to the pushforward along `i'`, for
`i ≫ e = i'` with `e` a monomorphism. -/
def map (h : i ≫ e = i') : monoPushforward i u₀ ⟶ monoPushforward i' u₀ where
  app T := ↾fun s ↦ mapSection e h (T := T.unop) s
  naturality T T₁ k := by
    ext s
    change mapSection e h (s.restrict k.unop) = (mapSection e h s).restrict k.unop
    refine MonoPushforwardSection.ext ?_ rfl
    exact NatTrans.naturality_apply e k s.base

/-- `map e h` acts on a section by `mapSection e h`. -/
@[simp]
lemma map_app_apply (h : i ≫ e = i') (T : Cᵒᵖ) (s : MonoPushforwardSection i u₀ T.unop) :
    (map e h).app T s = mapSection e h (T := T.unop) s := rfl

/-- `map e h` lies over `e`: followed by the projection to `F'` it is the projection to `F`
followed by `e`. -/
lemma map_π (h : i ≫ e = i') : map (u₀ := u₀) e h ≫ π i' u₀ = π i u₀ ≫ e := by
  ext T s
  rfl

/-- `map e h` carries the unit of the pushforward along `i` to that along `i'`. -/
lemma unit_map (h : i ≫ e = i') : unit i u₀ ≫ map e h = unit i' u₀ := by
  ext T a
  show mapSection e h (unitSection i u₀ (T := T.unop) a) = unitSection i' u₀ a
  refine MonoPushforwardSection.ext ?_ rfl
  show e.app T (i.app T (u₀.app T a)) = i'.app T (u₀.app T a)
  rw [← h]
  rfl

/-- **Pushing forward along `i` and along `i ≫ e` gives a cartesian square over `e`**, for a
monomorphism `e`: a section of the pushforward along `i'` whose underlying section comes from
`F` is a section of the pushforward along `i`, with the same lift. -/
theorem isPullback_map (h : i ≫ e = i') :
    IsPullback (map (u₀ := u₀) e h) (π i u₀) (π i' u₀) e := by
  refine IsPullback.of_forall_isPullback_app fun T ↦ ?_
  have hinj := injective_app_of_mono e T
  rw [Types.isPullback_iff]
  refine ⟨by rw [← NatTrans.comp_app, ← NatTrans.comp_app, map_π], ?_, ?_⟩
  · rintro s₁ s₂ ⟨h₁, h₂⟩
    exact MonoPushforwardSection.ext h₂
      (congrArg (fun s : MonoPushforwardSection i' u₀ T.unop ↦ s.sect) h₁)
  · intro s' b hb
    change s'.base = e.app T b at hb
    let s : MonoPushforwardSection i u₀ T.unop :=
      { base := b
        sect := s'.sect
        isSome_sect_iff := fun T' g ↦ by
          rw [s'.isSome_sect_iff, hb, ← NatTrans.naturality_apply e g.op b,
            mem_range_app_iff_of_mono e h]
        sect_over := fun T' g a ha ↦ by
          have h₀ := s'.sect_over g a ha
          rw [hb, ← NatTrans.naturality_apply e g.op b, ← h] at h₀
          exact injective_app_of_mono e _ h₀
        sect_comp := s'.sect_comp }
    exact ⟨s, MonoPushforwardSection.ext hb.symm rfl, rfl⟩

end monoPushforward

section Diagram

variable {Λ : Type*} [Preorder Λ] (P : Λ ⥤ Cᵒᵖ ⥤ Type (max w v)) (o : Λ) (ho : ∀ j, o ≤ j)
  (hmono : ∀ ⦃j j' : Λ⦄ (f : j ⟶ j'), Mono (P.map f)) (u₀ : C₀ ⟶ P.obj o)

/-- **The transport of `u₀ : C₀ ⟶ P o` to every stage of `P`.** For a diagram `P` of presheaves
with monomorphic transitions over a preorder with least element `o`, the stage `j` is the
pushforward of `u₀` along `P o ⟶ P j`, and the transitions are
`CategoryTheory.monoPushforward.map`. -/
def monoPushforwardDiagram : Λ ⥤ Cᵒᵖ ⥤ Type (max w v) where
  obj j := monoPushforward (P.map (homOfLE (ho j))) u₀
  map {j j'} f :=
    haveI := hmono f
    monoPushforward.map (P.map f) (by
      rw [← P.map_comp]
      exact congrArg P.map (Subsingleton.elim _ _))
  map_id j := by
    ext T s
    refine MonoPushforwardSection.ext ?_ rfl
    change (P.map (𝟙 j)).app T s.base = s.base
    simp
  map_comp f g := by
    ext T s
    refine MonoPushforwardSection.ext ?_ rfl
    change (P.map (f ≫ g)).app T s.base = (P.map g).app T ((P.map f).app T s.base)
    simp

/-- The projection of `CategoryTheory.monoPushforwardDiagram` to the diagram `P`. -/
def monoPushforwardDiagramπ : monoPushforwardDiagram P o ho hmono u₀ ⟶ P where
  app j := monoPushforward.π _ u₀
  naturality {j j'} f := by
    have := hmono f
    exact monoPushforward.map_π (P.map f) _

/-- The stage `j` of `monoPushforwardDiagram` is the pushforward of `u₀` along `P o ⟶ P j`. -/
@[simp]
lemma monoPushforwardDiagram_obj (j : Λ) :
    (monoPushforwardDiagram P o ho hmono u₀).obj j =
      monoPushforward (P.map (homOfLE (ho j))) u₀ := rfl

/-- The component at `j` of `monoPushforwardDiagramπ` is the projection of the pushforward to
`P j`. -/
@[simp]
lemma monoPushforwardDiagramπ_app (j : Λ) :
    (monoPushforwardDiagramπ P o ho hmono u₀).app j = monoPushforward.π _ u₀ := rfl

/-- **The transported charts form an equifibered diagram over `P`**: every transition square is
cartesian (`CategoryTheory.monoPushforward.isPullback_map`). -/
theorem monoPushforwardDiagram_equifibered :
    (monoPushforwardDiagramπ P o ho hmono u₀).Equifibered := by
  intro j j' f
  have := hmono f
  exact monoPushforward.isPullback_map (P.map f) _

end Diagram

end CategoryTheory

end
