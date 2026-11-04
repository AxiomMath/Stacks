module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import StacksCore.Tactic.StacksAttribute

/-!
# The localization at a right multiplicative system commutes with finite limits (Stacks 05Q6)

Let `W` be a right multiplicative system on a category `C`, i.e. one with a right calculus
of fractions, and let `L : C ⥤ D` be a localization of `C` at `W`. Then `L` preserves
finite limits; specialising to `L = W.Q` gives Stacks 05Q6. Note that the statement does
not claim that `W⁻¹C` *has* finite limits: it says only that a finite limit cone of `C` is
carried to a limit cone.

The proof is the filtered-colimit argument. Hom-sets in the localization are filtered
colimits of hom-sets of `C`: a morphism `L Z ⟶ L Y` is the value `(L f)(L s)⁻¹` of a right
fraction `Z ⟵s Z' ⟶f Y`, two such values agree iff their numerators agree after a further
refinement of the denominator, and finitely many of them can be put over a common
denominator. Since finite limits commute with filtered colimits in `Type`, each covariant
hom functor `Y ↦ Hom_D(P, L Y)` therefore preserves finite limits, and then so does `L`
itself, because a cone in `D` is a limit as soon as every covariant representable carries
it to a limit cone of types (`coyonedaJointlyReflectsLimits`).

Rather than build the colimit presentation as such, the argument here is elementwise, via
`Types.isLimit_iff`: for a finite diagram `K : J ⥤ C` with limit cone `c`, a section of the
hom functor is a family of morphisms `L Z ⟶ L (K.obj j)`; `exists_common_denominator` puts
them over one denominator `s`, `exists_simultaneous_refinement` refines `s` once more so
that the numerators form an honest cone over `K` — this is where the right Ore condition
and right cancellability are used — and lifting that cone through `c` produces the required
element. Uniqueness is the same two lemmas followed by `IsLimit.hom_ext`.

Mathlib has only `Localization.preservesFiniteProducts`, for products and under stability
hypotheses, so the finite-limit statement for a right calculus of fractions is proved here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

section Fractions


variable {C : Type*} [Category C] {D : Type*} [Category D]
  (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
  (L : C ⥤ D) [L.IsLocalization W]

/-- The value `(L f)(L s)⁻¹ : L X ⟶ L Y` in `D` of a right fraction `X ⟵s X' ⟶f Y`. -/
noncomputable abbrev RightFraction.value {X Y : C} (φ : W.RightFraction X Y) : L.obj X ⟶ L.obj Y :=
  φ.map L Functor.IsLocalization.inverts

/-- The value of `(s, f)` satisfies `L s ≫ value = L f`. -/
private theorem RightFraction.map_s_comp_value {C : Type*} [Category C] {D : Type*} [Category D]
    (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W] {Z Y Z' : C} (s : Z' ⟶ Z)
    (hs : W s) (f : Z' ⟶ Y) : L.map s ≫ RightFraction.value W L (.mk s hs f) = L.map f :=
  RightFraction.map_s_comp_map (RightFraction.mk s hs f) L Functor.IsLocalization.inverts

/-- The value of `(s, f)` is the unique `y` with `L s ≫ y = L f`. -/
private theorem RightFraction.value_eq_of_map_s_comp_eq {C : Type*} [Category C] {D : Type*}
    [Category D] (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W] {Z Y Z' : C}
    (s : Z' ⟶ Z) (hs : W s) (f : Z' ⟶ Y) (y : L.obj Z ⟶ L.obj Y) (h : L.map s ≫ y = L.map f) :
    RightFraction.value W L (.mk s hs f) = y := by
  have : IsIso (L.map s) := Functor.IsLocalization.inverts (W := W) s hs
  rw [← cancel_epi (L.map s), h, RightFraction.map_s_comp_value]

omit [W.HasRightCalculusOfFractions] in
/-- Refining a denominator does not change the value: if `s : Z' ⟶ Z` is in `W`,
`f : Z' ⟶ Y`, and `u : Z'' ⟶ Z'` with `W (u ≫ s)`, then the fraction `(u ≫ s, u ≫ f)`
has the same value as `(s, f)`. -/
theorem RightFraction.value_refine {Z Y : C} {Z' : C} (s : Z' ⟶ Z) (hs : W s) (f : Z' ⟶ Y)
    {Z'' : C} (u : Z'' ⟶ Z') (hus : W (u ≫ s)) :
    RightFraction.value W L (.mk (u ≫ s) hus (u ≫ f)) = RightFraction.value W L (.mk s hs f) := by
  refine RightFraction.value_eq_of_map_s_comp_eq W L _ hus _ _ ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc,
    RightFraction.map_s_comp_value W L s hs f]

omit [W.HasRightCalculusOfFractions] in
/-- The value of a right fraction depends on its denominator only through the underlying
morphism: equal denominators give equal values, whichever witnesses of membership in `W`
they carry. -/
theorem RightFraction.value_congr_denom {Z Y Z' : C} {s s' : Z' ⟶ Z} (hs : W s) (hs' : W s')
    (f : Z' ⟶ Y) (h : s = s') :
    RightFraction.value W L (.mk s hs f) = RightFraction.value W L (.mk s' hs' f) := by
  subst h
  rfl

omit [W.HasRightCalculusOfFractions] in
/-- Postcomposing the value of a fraction by `L φ` gives the value of the fraction with
numerator `f ≫ φ`. -/
theorem RightFraction.value_comp {Z Y Y' : C} {Z' : C} (s : Z' ⟶ Z) (hs : W s) (f : Z' ⟶ Y)
    (φ : Y ⟶ Y') :
    RightFraction.value W L (.mk s hs f) ≫ L.map φ =
      RightFraction.value W L (.mk s hs (f ≫ φ)) := by
  symm
  refine RightFraction.value_eq_of_map_s_comp_eq W L s hs _ _ ?_
  rw [← Category.assoc, RightFraction.map_s_comp_value W L s hs f, Functor.map_comp]

/-- Two fractions with the same denominator `s ∈ W` have the same value only if their
numerators agree after a refinement: there is `u : Z'' ⟶ Z'` with `W (u ≫ s)` and
`u ≫ f = u ≫ g`. -/
theorem RightFraction.exists_refinement_of_value_eq {Z Y : C} {Z' : C}
    (s : Z' ⟶ Z) (hs : W s) (f g : Z' ⟶ Y)
    (h : RightFraction.value W L (.mk s hs f) = RightFraction.value W L (.mk s hs g)) :
    ∃ (Z'' : C) (u : Z'' ⟶ Z'), W (u ≫ s) ∧ u ≫ f = u ≫ g := by
  rw [RightFraction.map_eq_iff L W] at h
  obtain ⟨Zt, t₁, t₂, hst, hfg, hWt⟩ := h
  dsimp only [RightFraction.mk] at hst hfg hWt
  obtain ⟨X', r, hWr, hr⟩ := HasRightCalculusOfFractions.ext (W := W) t₁ t₂ s hs hst
  refine ⟨X', r ≫ t₁, by simpa using W.comp_mem _ _ hWr hWt, ?_⟩
  rw [Category.assoc, hfg, ← Category.assoc, hr]

/-- **One value over a refinement of a given denominator.** Given a denominator `s : Z₁ ⟶ Z`
in `W` and a single value `x : Hom_D(L Z, L Y₀)`, the right Ore condition refines `s` by some
`t : Z₂ ⟶ Z₁` over which `x` acquires a numerator: `x` is the value of `(t ≫ s, g)`. -/
theorem exists_numerator_of_refine {Z Y₀ Z₁ : C} (s : Z₁ ⟶ Z) (hs : W s)
    (x : L.obj Z ⟶ L.obj Y₀) :
    ∃ (Z₂ : C) (t : Z₂ ⟶ Z₁) (hts : W (t ≫ s)) (g : Z₂ ⟶ Y₀),
      x = RightFraction.value W L (.mk (t ≫ s) hts g) := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L W x
  -- Right Ore (RMS2) merges the denominator `φ.s` of a fraction for `x` with `s`.
  obtain ⟨ψ, hψ⟩ := HasRightCalculusOfFractions.exists_rightFraction (W := W)
    (LeftFraction.mk (X := Z₁) (Y := φ.X') s φ.s φ.hs)
  have hmerge : ψ.s ≫ s = ψ.f ≫ φ.s := by simpa using hψ
  have hsW : W (ψ.s ≫ s) := W.comp_mem _ _ ψ.hs hs
  have hsW' : W (ψ.f ≫ φ.s) := hmerge ▸ hsW
  exact ⟨ψ.X', ψ.s, hsW, ψ.f ≫ φ.f, hφ.trans <|
    (RightFraction.value_refine W L φ.s φ.hs φ.f ψ.f hsW').symm.trans
      (RightFraction.value_congr_denom W L hsW' hsW (ψ.f ≫ φ.f) hmerge.symm)⟩

/-- **A common denominator for a finite family.** Given finitely many
`Y : ι → C` (ι a `Fintype`) and values `x i : Hom_D(L Z, L (Y i))`, there is a single
denominator `s : Z' ⟶ Z` in `W` and numerators `g i : Z' ⟶ Y i` representing each `x i`.
-/
@[sga "4 VI 6.5" "Clause b)", sga "4½ Etat_0 2.3.2" "partial"]
theorem exists_common_denominator {Z : C} {ι : Type*} [Finite ι] (Y : ι → C)
    (x : ∀ i, L.obj Z ⟶ L.obj (Y i)) :
    ∃ (Z' : C) (s : Z' ⟶ Z) (_ : W s) (g : ∀ i, Z' ⟶ Y i),
      ∀ i, x i = RightFraction.value W L (.mk s ‹W s› (g i)) := by
  have := Fintype.ofFinite ι
  -- Induct with the numerator quantified *inside* the family, so that reindexing along an
  -- equivalence of index types needs no transport; `Classical.skolem` then collects the
  -- numerators into a family `g`.
  suffices h : ∃ (Z' : C) (s : Z' ⟶ Z) (hs : W s),
      ∀ i, ∃ g : Z' ⟶ Y i, x i = RightFraction.value W L (.mk s hs g) by
    obtain ⟨Z', s, hs, h⟩ := h
    exact ⟨Z', s, hs, Classical.skolem.1 h⟩
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ (Y : ι → C) (x : ∀ i, L.obj Z ⟶ L.obj (Y i)),
      ∃ (Z' : C) (s : Z' ⟶ Z) (hs : W s),
        ∀ i, ∃ g : Z' ⟶ Y i, x i = RightFraction.value W L (.mk s hs g))
    ?_ ?_ ?_ ι Y x
  · -- transport along an equivalence `e : α ≃ β`
    intro α β _ e ih Y x
    obtain ⟨Z', s, hs, hg⟩ := ih (fun a => Y (e a)) (fun a => x (e a))
    refine ⟨Z', s, hs, fun i => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective i
    exact hg a
  · -- base case: `ι` empty.  Take `Z' = Z`, `s = 𝟙 Z`.
    intro Y x
    exact ⟨Z, 𝟙 Z, W.id_mem Z, fun i => i.elim⟩
  · -- step: add one element via `Option`, refining the denominator got so far.
    intro α _ ih Y x
    obtain ⟨Z₁, s₁, hs₁, hg₁⟩ := ih (fun a => Y (some a)) (fun a => x (some a))
    obtain ⟨Z₂, t, hts, g₀, hg₀⟩ := exists_numerator_of_refine W L s₁ hs₁ (x none)
    refine ⟨Z₂, t ≫ s₁, hts, ?_⟩
    rintro (_ | a)
    · exact ⟨g₀, hg₀⟩
    · obtain ⟨g, hg⟩ := hg₁ a
      exact ⟨t ≫ g, by rw [hg, ← RightFraction.value_refine W L s₁ hs₁ g t hts]⟩

/-- **Two refinements of a denominator have a common refinement.** If `w₁` and `w₂` both refine
a denominator `s : Z' ⟶ Z` of `W`, in the sense that `W (w₁ ≫ s)` and `W (w₂ ≫ s)`, then there
are `t₁` and `t₂` with `t₁ ≫ w₁ = t₂ ≫ w₂` again refining `s`. This is the right Ore condition
followed by right cancellability of `s`. -/
@[sga "4 VI 6.5" "Cofilteredness of S(X)"]
theorem exists_common_refinement {Z Z' : C} (s : Z' ⟶ Z) (hs : W s) {Z₁ Z₂ : C}
    (w₁ : Z₁ ⟶ Z') (w₂ : Z₂ ⟶ Z') (h₁ : W (w₁ ≫ s)) (h₂ : W (w₂ ≫ s)) :
    ∃ (Z₀ : C) (t₁ : Z₀ ⟶ Z₁) (t₂ : Z₀ ⟶ Z₂),
      t₁ ≫ w₁ = t₂ ≫ w₂ ∧ W ((t₁ ≫ w₁) ≫ s) := by
  -- Right Ore (RMS2) merges the denominators `w₁ ≫ s` and `w₂ ≫ s` over `Z`.
  obtain ⟨ψ, hψ⟩ := HasRightCalculusOfFractions.exists_rightFraction (W := W)
    (LeftFraction.mk (X := Z₁) (Y := Z₂) (w₁ ≫ s) (w₂ ≫ s) h₂)
  -- Right cancellability (RMS3) then removes `s`.
  obtain ⟨Z₀, t, hWt, ht⟩ := HasRightCalculusOfFractions.ext (W := W)
    (ψ.s ≫ w₁) (ψ.f ≫ w₂) s hs (by simpa [Category.assoc] using hψ)
  refine ⟨Z₀, t ≫ ψ.s, t ≫ ψ.f, by simpa [Category.assoc] using ht, ?_⟩
  simpa using W.comp_mem _ _ (W.comp_mem _ _ hWt ψ.hs) h₁

/-- **Simultaneous refinement of finitely many equalities.** Given a
denominator `s : Z' ⟶ Z ∈ W` and finitely many parallel pairs `α m, β m : Z' ⟶ T m`,
each equalisable by some refinement `u m` (with `W (u m ≫ s)` and `u m ≫ α m = u m ≫ β m`),
there is a single refinement `w : Z'' ⟶ Z'` with `W (w ≫ s)` equalising all of them. -/
theorem exists_simultaneous_refinement {Z : C} {Z' : C} (s : Z' ⟶ Z) (hs : W s)
    {ι : Type*} [Finite ι] {T : ι → C} (α β : ∀ i, Z' ⟶ T i)
    (hrefine : ∀ i, ∃ (Zi : C) (ui : Zi ⟶ Z'), W (ui ≫ s) ∧ ui ≫ α i = ui ≫ β i) :
    ∃ (Z'' : C) (w : Z'' ⟶ Z'), W (w ≫ s) ∧ ∀ i, w ≫ α i = w ≫ β i := by
  have := Fintype.ofFinite ι
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ {T : ι → C} (α β : ∀ i, Z' ⟶ T i),
      (∀ i, ∃ (Zi : C) (ui : Zi ⟶ Z'), W (ui ≫ s) ∧ ui ≫ α i = ui ≫ β i) →
      ∃ (Z'' : C) (w : Z'' ⟶ Z'), W (w ≫ s) ∧ ∀ i, w ≫ α i = w ≫ β i)
    ?_ ?_ ?_ ι α β hrefine
  · -- transport along an equivalence `e : a ≃ b`
    intro a b _ e ih T α β hrefine
    obtain ⟨Z'', w, hw, hweq⟩ := ih (T := fun x => T (e x)) (fun x => α (e x))
      (fun x => β (e x)) (fun x => hrefine (e x))
    refine ⟨Z'', w, hw, fun i => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective i
    exact hweq x
  · -- base case: `ι` empty.  Take `Z'' = Z'`, `w = 𝟙 Z'`.
    intro T α β _
    exact ⟨Z', 𝟙 Z', by rwa [Category.id_comp], fun i => i.elim⟩
  · -- step: add one element via `Option`, merging its refinement with the one got so far.
    intro a _ ih T α β hrefine
    obtain ⟨Z₀, w₀, hw₀, hw₀eq⟩ := ih (T := fun x => T (some x))
      (fun x => α (some x)) (fun x => β (some x)) (fun x => hrefine (some x))
    obtain ⟨Zu, u, hWu, hueq⟩ := hrefine none
    obtain ⟨Xt, t₀, tu, ht, hsW⟩ := exists_common_refinement W s hs w₀ u hw₀ hWu
    refine ⟨Xt, t₀ ≫ w₀, hsW, ?_⟩
    rintro (_ | x)
    · rw [ht, Category.assoc, Category.assoc, hueq]
    · rw [Category.assoc, Category.assoc, hw₀eq x]

include W in
/-- **A compatible family into a finite limit cone is induced by a map to the apex.**
Let `c` be a limit cone over a finite diagram `K : J ⥤ C` and let `x j : Hom_D(L Z, L (K.obj j))`
be compatible with the maps of `K`. Then some `y : L Z ⟶ L c.pt` satisfies
`y ≫ L (c.π.app j) = x j` for every `j`.

The family is put over a common denominator, that denominator is refined once so that the
numerators form an honest cone over `K`, and the cone is lifted through `c`. -/
theorem exists_hom_of_isLimit {Z : C} {J : Type} [SmallCategory J] [FinCategory J]
    {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (x : ∀ j, L.obj Z ⟶ L.obj (K.obj j))
    (hx : ∀ {i j : J} (φ : i ⟶ j), x i ≫ L.map (K.map φ) = x j) :
    ∃ y : L.obj Z ⟶ L.obj c.pt, ∀ j, y ≫ L.map (c.π.app j) = x j := by
  obtain ⟨Z', s₀, hs₀, g, hg⟩ := exists_common_denominator W L K.obj x
  -- Compatibility makes `g i ≫ K.map φ` and `g j` agree after a refinement, for each `φ`;
  -- one refinement `w` does all of them at once.
  obtain ⟨Z'', w, hw, hweq⟩ :=
    exists_simultaneous_refinement W s₀ hs₀
      (T := fun (⟨⟨_, j⟩, _⟩ : Σ (p : J × J), (p.1 ⟶ p.2)) => K.obj j)
      (α := fun ⟨⟨i, _⟩, φ⟩ => g i ≫ K.map φ) (β := fun ⟨⟨_, j⟩, _⟩ => g j)
      (fun ⟨⟨i, j⟩, φ⟩ => by
        apply RightFraction.exists_refinement_of_value_eq W L s₀ hs₀
        rw [← RightFraction.value_comp W L s₀ hs₀ (g i) (K.map φ), ← hg i, ← hg j, hx φ])
  let cwK : Cone K :=
    { pt := Z''
      π :=
        { app := fun j => w ≫ g j
          naturality := fun i j φ => by
            dsimp
            rw [Category.id_comp, Category.assoc]
            exact (hweq ⟨(i, j), φ⟩).symm } }
  refine ⟨RightFraction.value W L (.mk (w ≫ s₀) hw (hc.lift cwK)), fun j => ?_⟩
  rw [RightFraction.value_comp W L (w ≫ s₀) hw (hc.lift cwK) (c.π.app j), hc.fac cwK j,
    RightFraction.value_refine W L s₀ hs₀ (g j) w hw, ← hg j]

include W in
/-- **Maps to the apex of a finite limit cone are determined by their projections.**
Two morphisms `y₁ y₂ : L Z ⟶ L c.pt` into the image of the apex of a limit cone over a finite
diagram agree as soon as `y₁ ≫ L (c.π.app j) = y₂ ≫ L (c.π.app j)` for every `j`. Note that this
is not the localization functor reflecting the limit: it is proved by putting `y₁` and `y₂` over a
common denominator and refining once, as in `exists_hom_of_isLimit`. -/
theorem hom_ext_of_isLimit {Z : C} {J : Type} [SmallCategory J] [FinCategory J]
    {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (y₁ y₂ : L.obj Z ⟶ L.obj c.pt)
    (h : ∀ j, y₁ ≫ L.map (c.π.app j) = y₂ ≫ L.map (c.π.app j)) : y₁ = y₂ := by
  obtain ⟨Z₃, σ, hσ, p, hp⟩ :=
    exists_common_denominator W L (fun _ : Fin 2 => c.pt) (fun i => if i = 0 then y₁ else y₂)
  have h₁ : y₁ = RightFraction.value W L (.mk σ hσ (p 0)) := by simpa using hp 0
  have h₂ : y₂ = RightFraction.value W L (.mk σ hσ (p 1)) := by simpa using hp 1
  obtain ⟨Z₄, v, hv, hveq⟩ :=
    exists_simultaneous_refinement W σ hσ
      (α := fun j : J => p 0 ≫ c.π.app j) (β := fun j : J => p 1 ≫ c.π.app j)
      (fun j => by
        apply RightFraction.exists_refinement_of_value_eq W L σ hσ
        rw [← RightFraction.value_comp W L σ hσ (p 0) (c.π.app j),
          ← RightFraction.value_comp W L σ hσ (p 1) (c.π.app j), ← h₁, ← h₂, h j])
  -- `v ≫ p 0` and `v ≫ p 1` agree after every projection of `c`, hence are equal.
  have hpe : v ≫ p 0 = v ≫ p 1 :=
    hc.hom_ext fun j => by simpa using hveq j
  rw [h₁, h₂, ← RightFraction.value_refine W L σ hσ (p 0) v hv,
    ← RightFraction.value_refine W L σ hσ (p 1) v hv, hpe]

end Fractions

/-- The case `P = L Z` of `preservesFiniteLimits_comp_coyoneda`, which carries all of the
content: the covariant hom functor `Y ↦ Hom_D(L Z, L Y)` preserves finite limits. -/
theorem preservesFiniteLimits_comp_coyoneda_obj_map
    {C : Type*} [Category C] {D : Type*} [Category D]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (L : C ⥤ D) [L.IsLocalization W] (Z : C) :
    PreservesFiniteLimits (L ⋙ coyoneda.obj (Opposite.op (L.obj Z))) := by
  -- Elementwise, via `Types.isLimit_iff`: existence of the lift is `exists_hom_of_isLimit` and
  -- its uniqueness is `hom_ext_of_isLimit`.
  apply PreservesFiniteLimits.mk
  intro J _ _
  apply PreservesLimitsOfShape.mk
  intro K
  apply PreservesLimit.mk
  intro c hc
  rw [Types.isLimit_iff]
  -- `x` is a section of `K ⋙ L ⋙ coyoneda.obj (op (L Z))`; the section condition
  -- (after `rfl`-level normalization) reads `x i ≫ L.map (K.map φ) = x j`.
  intro x hx
  obtain ⟨y, hy⟩ := exists_hom_of_isLimit W L hc x fun φ => hx φ
  exact ⟨y, hy, fun y' hy' =>
    hom_ext_of_isLimit W L hc y' y fun j => (hy' j).trans (hy j).symm⟩

/-- The covariant hom functor `Y ↦ Hom_D(P, L Y)` preserves finite limits for an arbitrary
`P : D`, not just for `P` of the form `L Z`: a localization is essentially surjective, so
`P ≅ L Z` for some `Z`, and `preservesFiniteLimits_comp_coyoneda_obj_map` transports along the
induced natural isomorphism of hom functors. -/
theorem preservesFiniteLimits_comp_coyoneda
    {C : Type*} [Category C] {D : Type*} [Category D]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (L : C ⥤ D) [L.IsLocalization W] (P : D) :
    PreservesFiniteLimits (L ⋙ coyoneda.obj (Opposite.op P)) := by
  -- Every `P : D` is isomorphic to some `L.obj Z`, localizations being essentially
  -- surjective; transport along the induced natural iso of hom functors.
  obtain ⟨Z, ⟨e⟩⟩ := (Localization.essSurj L W).mem_essImage P
  have := preservesFiniteLimits_comp_coyoneda_obj_map W L Z
  exact preservesFiniteLimits_of_natIso
    (Functor.isoWhiskerLeft L (coyoneda.mapIso (Iso.op e.symm)))

/-- A localization functor at a right multiplicative system preserves finite limits. -/
theorem preservesFiniteLimits_of_hasRightCalculusOfFractions
    {C : Type*} [Category C] {D : Type*} [Category D]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (L : C ⥤ D) [L.IsLocalization W] :
    PreservesFiniteLimits L := by
  constructor
  intro J _ _
  constructor
  intro F
  constructor
  intro c hc
  -- A cone in `D` is a limit iff every covariant representable sends it to a limit
  -- cone in `Type` (`coyonedaJointlyReflectsLimits`).
  refine ⟨coyonedaJointlyReflectsLimits _ (L.mapCone c) fun P => ?_⟩
  -- `(coyoneda.obj P).mapCone (L.mapCone c) = (L ⋙ coyoneda.obj P).mapCone c`, which is a
  -- limit because `L ⋙ coyoneda.obj P` preserves the finite limit `c`.
  have := preservesFiniteLimits_comp_coyoneda W L P.unop
  exact isLimitOfPreserves (L ⋙ coyoneda.obj P) hc

/-- **Stacks 05Q6.** For a right multiplicative system `W` on `C`, the localization functor
`Q : C ⥤ W⁻¹C` commutes with finite limits. This does not assert that `W⁻¹C` has finite
limits: only that `Q` carries a finite limit cone of `C` to a limit cone. -/
@[stacks 05Q6]
theorem Q_preservesFiniteLimits
    {C : Type*} [Category C] (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] :
    PreservesFiniteLimits W.Q :=
  preservesFiniteLimits_of_hasRightCalculusOfFractions W W.Q

end CategoryTheory.MorphismProperty
