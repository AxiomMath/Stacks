module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import StacksFrontier.Topology.Sheaves.StalkOfSize

/-!
# The pullback of a sheaf of sets, realised as a sheaf of germs

Let `g : Z → Y` be a continuous map and let `𝒢` be a presheaf of types on `Y`.  The pullback
`g⁻¹𝒢` is realised here in the classical way, as the sheaf of continuous sections of the
pullback of the espace étalé of `𝒢`: a section of `g⁻¹𝒢` over `W ⊆ Z` is a function
`σ : W → Germs 𝒢` into the total space of germs of `𝒢`, which is *locally* of the form
`z ↦ ⟨g z, germ_{g z} s⟩` for a section `s` of `𝒢` on an open of `Y` containing the image.
This is `TopCat.subsheafToTypes` applied to the sheafification of the prelocal predicate
`GermPullback.pre g 𝒢`. The fibre type `Germs 𝒢` does not depend on `g`, so pullback along a
further map `h : Z' → Z` is precomposition with `h`, and the value of a section at a point is its
germ there.

## Main definitions

* `GermPullback.Germs 𝒢`: the total space of germs of `𝒢`.
* `GermPullback.sheaf g 𝒢`: the pullback `g⁻¹𝒢`, a sheaf of types on `Z`.
* `GermPullback.ofSection`: the germwise pullback `𝒢(V) → (g⁻¹𝒢)(W)` for `W ⊆ g⁻¹(V)`.
* `GermPullback.comap`: pullback of sections along a further map, i.e. precomposition.

## Main results

* `GermPullback.eventually_eq_of_apply_eq`: two sections whose germs at a point agree already
  agree on a neighbourhood of that point.
* `GermPullback.isOpen_agreeSet`: the locus in `W` where two sections of `g⁻¹𝒢` have the same
  germ is open, so the locus where they differ is closed in `W`.
* `GermPullback.comap_comp`, `GermPullback.comap_id`: strict functoriality of `comap`.
* `GermPullback.exists_glue`: sections on the members of an open covering that agree pointwise on
  the overlaps glue.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u t

noncomputable section

namespace GermPullback

variable {Y Z Z' Z'' : TopCat.{u}}

/-- The total space of germs of a presheaf of types `𝒢` on `Y`: a point of `Y` together with an
element of the stalk of `𝒢` there. -/
def Germs (𝒢 : Y.Presheaf (Type (max u t))) : Type (max u t) := Σ y : Y, 𝒢.stalkOfSize y

/-- Two germs of the same section of `𝒢`, taken at equal points, are equal. -/
lemma Germs.mk_eq_mk {𝒢 : Y.Presheaf (Type (max u t))} {V : Opens Y} (s : 𝒢.obj (op V))
    {y y' : Y} (e : y = y') (hy : y ∈ V) (hy' : y' ∈ V) :
    (⟨y, 𝒢.germOfSize V y hy s⟩ : Germs 𝒢) = ⟨y', 𝒢.germOfSize V y' hy' s⟩ := by
  subst e; rfl

/-- The prelocal predicate on `Germs 𝒢`-valued functions on `Z` which says that the function is
the family of germs of a single section of `𝒢` defined on an open containing the image. -/
def pre (g : Z → Y) (𝒢 : Y.Presheaf (Type (max u t))) :
    PrelocalPredicate (fun _ : Z ↦ Germs 𝒢) where
  pred {W} σ := ∃ (V : Opens Y) (hV : ∀ z : W, g z.1 ∈ V) (s : 𝒢.obj (op V)),
    ∀ z : W, σ z = ⟨g z.1, 𝒢.germOfSize V (g z.1) (hV z) s⟩
  res i σ h := by
    obtain ⟨V, hV, s, hs⟩ := h
    exact ⟨V, fun z ↦ hV (i z), s, fun z ↦ hs (i z)⟩

/-- The pullback `g⁻¹𝒢` of a presheaf of types along `g : Z → Y`: the sheaf of functions to the
total space of germs of `𝒢` which are locally the germs of a single section of `𝒢`. -/
def sheaf (g : Z → Y) (𝒢 : Y.Presheaf (Type (max u t))) : Z.Sheaf (Type (max u t)) :=
  subsheafToTypes (pre g 𝒢).sheafify

variable {g : Z → Y} {𝒢 : Y.Presheaf (Type (max u t))}

/-- Sections of `g⁻¹𝒢` are functions to `Germs 𝒢`, so two of them agreeing pointwise are
equal. -/
lemma ext {W : Opens Z} {σ τ : (sheaf g 𝒢).presheaf.obj (op W)}
    (h : ∀ z : W, σ.1 z = τ.1 z) : σ = τ :=
  Subtype.ext (funext h)

/-- Restriction in `g⁻¹𝒢` along an inclusion `i : W' ⟶ W` of opens is computed pointwise: the
restricted section takes at `z ∈ W'` the value the original takes at `z` viewed in `W`. -/
@[simp]
lemma val_map_apply {W W' : Opens Z} (i : W' ⟶ W) (σ : (sheaf g 𝒢).presheaf.obj (op W)) (z : W') :
    ((sheaf g 𝒢).presheaf.map i.op σ).1 z = σ.1 (i z) := rfl

/-- Near every point, a section of `g⁻¹𝒢` is the family of germs of a section of `𝒢`. -/
lemma exists_repr {W : Opens Z} (σ : (sheaf g 𝒢).presheaf.obj (op W)) {z : Z} (hz : z ∈ W) :
    ∃ (W₀ : Opens Z) (_ : z ∈ W₀) (i : W₀ ⟶ W) (V : Opens Y) (hV : ∀ x : W₀, g x.1 ∈ V)
      (s : 𝒢.obj (op V)), ∀ x : W₀, σ.1 (i x) = ⟨g x.1, 𝒢.germOfSize V (g x.1) (hV x) s⟩ :=
  σ.2 ⟨z, hz⟩

/-- The germwise pullback of a section: if `g` maps `W` into `V`, then a section `s ∈ 𝒢(V)`
determines the section `z ↦ ⟨g z, germ_{g z} s⟩` of `g⁻¹𝒢` over `W`. -/
def ofSection {W : Opens Z} {V : Opens Y} (hV : ∀ z : W, g z.1 ∈ V) (s : 𝒢.obj (op V)) :
    (sheaf g 𝒢).presheaf.obj (op W) :=
  ⟨fun z ↦ ⟨g z.1, 𝒢.germOfSize V (g z.1) (hV z) s⟩,
    PrelocalPredicate.sheafifyOf (P := pre g 𝒢) ⟨V, hV, s, fun _ ↦ rfl⟩⟩

/-- The germwise pullback of `s ∈ 𝒢(V)` takes at `z ∈ W` the value `⟨g z, germ_{g z} s⟩`. -/
@[simp]
lemma ofSection_val {W : Opens Z} {V : Opens Y} (hV : ∀ z : W, g z.1 ∈ V) (s : 𝒢.obj (op V))
    (z : W) : (ofSection hV s).1 z = ⟨g z.1, 𝒢.germOfSize V (g z.1) (hV z) s⟩ := rfl

/-! ### Germs determine sections locally -/

/-- A section given on `A` by germs of `s ∈ 𝒢(V)` is also given by germs of any restriction of
`s` to `V' ⊆ V`, at points of `A` lying over `V'`. -/
private lemma sigma_apply_eq_germ_map {W A : Opens Z} {σ : ∀ _ : W, Germs 𝒢} {j : A ⟶ W}
    {V V' : Opens Y} {hV : ∀ x : A, g x.1 ∈ V} {s : 𝒢.obj (op V)}
    (hs : ∀ x : A, σ (j x) = ⟨g x.1, 𝒢.germOfSize V (g x.1) (hV x) s⟩) (k : V' ⟶ V) (x : A)
    (hx : g x.1 ∈ V') :
    σ (j x) = ⟨g x.1, 𝒢.germOfSize V' (g x.1) hx (𝒢.map k.op s)⟩ := by
  rw [hs x, 𝒢.germOfSize_res_apply]

/-- If two locally-germwise functions have the same value — that is, the same germ — at a point,
then they agree on a neighbourhood of that point.  This is the statement that the value of a
section of `g⁻¹𝒢` at `z` is its germ at `z`. -/
lemma eventually_eq_of_apply_eq (hg : Continuous g) {W₁ W₂ : Opens Z}
    {σ₁ : ∀ _ : W₁, Germs 𝒢} (h₁ : (pre g 𝒢).sheafify.pred σ₁)
    {σ₂ : ∀ _ : W₂, Germs 𝒢} (h₂ : (pre g 𝒢).sheafify.pred σ₂)
    {z : Z} (hz₁ : z ∈ W₁) (hz₂ : z ∈ W₂) (he : σ₁ ⟨z, hz₁⟩ = σ₂ ⟨z, hz₂⟩) :
    ∃ (W : Opens Z) (_ : z ∈ W) (i₁ : W ⟶ W₁) (i₂ : W ⟶ W₂),
      ∀ x : W, σ₁ (i₁ x) = σ₂ (i₂ x) := by
  obtain ⟨A₁, hzA₁, j₁, V₁, hV₁, s₁, hs₁⟩ := h₁ ⟨z, hz₁⟩
  obtain ⟨A₂, hzA₂, j₂, V₂, hV₂, s₂, hs₂⟩ := h₂ ⟨z, hz₂⟩
  have e₁ : σ₁ ⟨z, hz₁⟩ = ⟨g z, 𝒢.germOfSize V₁ (g z) (hV₁ ⟨z, hzA₁⟩) s₁⟩ := hs₁ ⟨z, hzA₁⟩
  have e₂ : σ₂ ⟨z, hz₂⟩ = ⟨g z, 𝒢.germOfSize V₂ (g z) (hV₂ ⟨z, hzA₂⟩) s₂⟩ := hs₂ ⟨z, hzA₂⟩
  have hgerm : 𝒢.germOfSize V₁ (g z) (hV₁ ⟨z, hzA₁⟩) s₁ =
      𝒢.germOfSize V₂ (g z) (hV₂ ⟨z, hzA₂⟩) s₂ :=
    eq_of_heq ((Sigma.mk.injEq _ _ _ _).mp (e₁.symm.trans (he.trans e₂))).2
  obtain ⟨V₃, hzV₃, k₁, k₂, hk⟩ :=
    𝒢.germOfSize_eq (g z) (hV₁ ⟨z, hzA₁⟩) (hV₂ ⟨z, hzA₂⟩) s₁ s₂ hgerm
  refine ⟨A₁ ⊓ A₂ ⊓ ⟨g ⁻¹' (V₃ : Set Y), V₃.isOpen.preimage hg⟩, ⟨⟨hzA₁, hzA₂⟩, hzV₃⟩,
    homOfLE (le_trans inf_le_left inf_le_left) ≫ j₁,
    homOfLE (le_trans inf_le_left inf_le_right) ≫ j₂, fun x ↦ ?_⟩
  have hxV₃ : g x.1 ∈ V₃ := x.2.2
  rw [Opens.comp_apply, Opens.comp_apply, Opens.apply_def (homOfLE _) x,
    Opens.apply_def (homOfLE _) x, sigma_apply_eq_germ_map hs₁ k₁ ⟨x.1, x.2.1.1⟩ hxV₃,
    sigma_apply_eq_germ_map hs₂ k₂ ⟨x.1, x.2.1.2⟩ hxV₃, hk]

/-- The locus of points of `Z` lying in `W` at which two sections of `g⁻¹𝒢` have the same germ
is open in `Z`; equivalently, inside `W` the locus where the germs differ is closed. -/
lemma isOpen_agreeSet (hg : Continuous g) {W : Opens Z} (σ τ : (sheaf g 𝒢).presheaf.obj (op W)) :
    IsOpen {z : Z | ∃ hz : z ∈ W, σ.1 ⟨z, hz⟩ = τ.1 ⟨z, hz⟩} := by
  rw [isOpen_iff_forall_mem_open]
  rintro z ⟨hzW, he⟩
  obtain ⟨W₀, hzW₀, i₁, i₂, hW₀⟩ := eventually_eq_of_apply_eq hg σ.2 τ.2 hzW hzW he
  exact ⟨(W₀ ⊓ W : Opens Z), fun x hx ↦ ⟨hx.2, hW₀ ⟨x, hx.1⟩⟩, (W₀ ⊓ W).isOpen, hzW₀, hzW⟩

/-- The locus in `W` on which two sections of `g⁻¹𝒢` have the same germ is open. -/
lemma isOpen_agree (hg : Continuous g) {W : Opens Z} (σ τ : (sheaf g 𝒢).presheaf.obj (op W)) :
    IsOpen {z : W | σ.1 z = τ.1 z} := by
  have h := (isOpen_agreeSet hg σ τ).preimage (continuous_subtype_val (p := (· ∈ W)))
  convert h using 1
  exact Set.ext fun z ↦ ⟨fun hz ↦ ⟨z.2, hz⟩, fun hz ↦ hz.2⟩

/-! ### Gluing sections -/

/-- Sections of `g⁻¹𝒢` over the members of an open covering of `W`, agreeing pointwise wherever
two members meet, glue to a section over `W`. -/
lemma exists_glue {W : Opens Z} {ι : Type*} (W' : ι → Opens Z) (hle : ∀ l, W' l ≤ W)
    (hcov : ∀ z ∈ W, ∃ l, z ∈ W' l)
    (σ : ∀ l, (sheaf g 𝒢).presheaf.obj (op (W' l)))
    (hagree : ∀ (l l' : ι) (z : Z) (hz : z ∈ W' l) (hz' : z ∈ W' l'),
      (σ l).1 ⟨z, hz⟩ = (σ l').1 ⟨z, hz'⟩) :
    ∃ ρ : (sheaf g 𝒢).presheaf.obj (op W),
      ∀ (l : ι) (z : Z) (hz : z ∈ W' l), ρ.1 ⟨z, hle l hz⟩ = (σ l).1 ⟨z, hz⟩ := by
  classical
  have hchoose : ∀ z : W, ∃ l, z.1 ∈ W' l := fun z ↦ hcov z.1 z.2
  set f : ∀ _ : W, Germs 𝒢 := fun z ↦ (σ (hchoose z).choose).1 ⟨z.1, (hchoose z).choose_spec⟩
    with hf
  have hval : ∀ (z : W) (l : ι) (hz : z.1 ∈ W' l), f z = (σ l).1 ⟨z.1, hz⟩ :=
    fun z l hz ↦ hagree _ l z.1 _ hz
  refine ⟨⟨f, fun z ↦ ?_⟩, fun l z hz ↦ hval ⟨z, hle l hz⟩ l hz⟩
  obtain ⟨V₀, hz₀, i₀, V, hV, s, hs⟩ := exists_repr (σ (hchoose z).choose) (hchoose z).choose_spec
  refine ⟨V₀, hz₀, i₀ ≫ homOfLE (hle (hchoose z).choose), V, hV, s, fun x ↦ ?_⟩
  exact (hval _ (hchoose z).choose (i₀ x).2).trans (hs x)

/-! ### Pullback of sections along a further map -/

variable {g' : Z' → Y} {h : Z' → Z}

/-- Pullback of a section along a further map: if `W' ⊆ h⁻¹(W)` and `g' = g ∘ h`, then
precomposition with `h` carries a section of `g⁻¹𝒢` over `W` to a section of `g'⁻¹𝒢` over
`W'`. -/
def comap (hh : Continuous h) (hcomp : ∀ z, g' z = g (h z)) {W : Opens Z} {W' : Opens Z'}
    (hW : ∀ z : W', h z.1 ∈ W) (σ : (sheaf g 𝒢).presheaf.obj (op W)) :
    (sheaf g' 𝒢).presheaf.obj (op W') := by
  refine ⟨fun z ↦ σ.1 ⟨h z.1, hW z⟩, fun z ↦ ?_⟩
  obtain ⟨W₀, hz₀, i, V, hV, s, hs⟩ := exists_repr σ (hW z)
  refine ⟨W' ⊓ ⟨h ⁻¹' (W₀ : Set Z), W₀.isOpen.preimage hh⟩, ⟨z.2, hz₀⟩,
    homOfLE inf_le_left, V, fun x ↦ ?_, s, fun x ↦ ?_⟩
  · rw [hcomp]
    exact hV ⟨h x.1, x.2.2⟩
  · exact (hs ⟨h x.1, x.2.2⟩).trans (Germs.mk_eq_mk s (hcomp x.1).symm _ _)

/-- `comap` is precomposition with `h`: the pulled-back section takes at `z ∈ W'` the value the
original section takes at `h z ∈ W`. -/
@[simp]
lemma comap_val (hh : Continuous h) (hcomp : ∀ z, g' z = g (h z)) {W : Opens Z} {W' : Opens Z'}
    (hW : ∀ z : W', h z.1 ∈ W) (σ : (sheaf g 𝒢).presheaf.obj (op W)) (z : W') :
    (comap hh hcomp hW σ).1 z = σ.1 ⟨h z.1, hW z⟩ := rfl

/-- `comap` along the identity, with `W' ≤ W`, is restriction. -/
lemma comap_id {W W' : Opens Z} (hW : ∀ z : W', z.1 ∈ W) (σ : (sheaf g 𝒢).presheaf.obj (op W)) :
    comap (g' := g) continuous_id (fun _ ↦ rfl) hW σ =
      (sheaf g 𝒢).presheaf.map (homOfLE (fun _ hx ↦ hW ⟨_, hx⟩) : W' ⟶ W).op σ :=
  rfl

/-- `comap` is strictly functorial: pulling back along `h` and then along `h''` is pulling back
along `h ∘ h''`. -/
lemma comap_comp {g'' : Z'' → Y} {h'' : Z'' → Z'} (hh : Continuous h) (hh'' : Continuous h'')
    (hcomp : ∀ z, g' z = g (h z)) (hcomp'' : ∀ z, g'' z = g' (h'' z))
    {W : Opens Z} {W' : Opens Z'} {W'' : Opens Z''}
    (hW : ∀ z : W', h z.1 ∈ W) (hW'' : ∀ z : W'', h'' z.1 ∈ W')
    (σ : (sheaf g 𝒢).presheaf.obj (op W)) :
    comap hh'' hcomp'' hW'' (comap hh hcomp hW σ) =
      comap (g' := g'') (hh.comp hh'') (fun z ↦ (hcomp'' z).trans (hcomp _))
        (fun z ↦ hW ⟨h'' z.1, hW'' z⟩) σ :=
  rfl

/-- `comap` depends only on the underlying map, so pointwise equal maps induce the same
pullback of sections. -/
lemma comap_congr {h₁ h₂ : Z' → Z} (hh₁ : Continuous h₁) (hh₂ : Continuous h₂)
    (hcomp₁ : ∀ z, g' z = g (h₁ z)) (hcomp₂ : ∀ z, g' z = g (h₂ z)) {W : Opens Z} {W' : Opens Z'}
    (hW₁ : ∀ z : W', h₁ z.1 ∈ W) (hW₂ : ∀ z : W', h₂ z.1 ∈ W) (e : ∀ z, h₁ z = h₂ z)
    (σ : (sheaf g 𝒢).presheaf.obj (op W)) :
    comap hh₁ hcomp₁ hW₁ σ = comap hh₂ hcomp₂ hW₂ σ := by
  refine ext fun z ↦ ?_
  rw [comap_val, comap_val]
  exact congrArg σ.1 (Subtype.ext (e z.1))

/-- Pulling back a germwise pullback of a section is the germwise pullback of that section. -/
lemma comap_ofSection (hh : Continuous h) (hcomp : ∀ z, g' z = g (h z)) {W : Opens Z}
    {W' : Opens Z'} (hW : ∀ z : W', h z.1 ∈ W) {V : Opens Y} (hV : ∀ z : W, g z.1 ∈ V)
    (s : 𝒢.obj (op V)) :
    comap hh hcomp hW (ofSection hV s) =
      ofSection (g := g') (fun z ↦ (hcomp z.1).symm ▸ hV ⟨h z.1, hW z⟩) s := by
  refine ext fun z ↦ ?_
  rw [comap_val, ofSection_val, ofSection_val]
  exact Germs.mk_eq_mk s (hcomp z.1).symm _ _

end GermPullback
