module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Density
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Covering a product or an equalizer of sheafified representables, morphism by morphism

Let `C` be a site and let `h_U^#` denote the sheafification of the presheaf represented by an
object `U`. Two surjectivity statements about sheafified representables are reduced here to
statements about the hom-sets of `C` alone.

* A finite family `V_i` with morphisms `p_i : V_i ⟶ X` and `q_i : V_i ⟶ X'` makes
  `∐_i h_{V_i}^# ⟶ h_X^# ⨯ h_{X'}^#` surjective as soon as every *pair* of morphisms
  `α : Y ⟶ X`, `β : Y ⟶ X'` of the site factors, locally on `Y`, through some `(p_i, q_i)`.
* A finite family `V_i` with morphisms `p_i : V_i ⟶ X` equalizing a pair `a, b : X ⟶ X'` makes
  `∐_i h_{V_i}^# ⟶ Equalizer(h_a^#, h_b^#)` surjective as soon as every morphism `α : Y ⟶ X` of
  the site *that equalizes `a` and `b`* factors, locally on `Y`, through some `p_i`.

These are conditions (3) and (4) of **Stacks 0GN4**, in the shape
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_globalSections_of_covers`
consumes them, with every mention of a sheaf removed from the hypothesis.

## Main results

* `CategoryTheory.Sheaf.exists_covering_sheafifiedYoneda_map_eq`: a morphism `h_Y^# ⟶ h_X^#` of
  sheafified representables is, locally on `Y`, the sheafified representable of a morphism of the
  site.
* `CategoryTheory.Sheaf.exists_covering_comp_eq_of_sheafifiedYoneda_map_eq`: two morphisms of the
  site with the same sheafified representable agree locally.
* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_exists_covering_anyIndex`:
  condition (3) of Stacks 0GN4 from a condition on pairs of morphisms of the site, for a family
  indexed by an arbitrary type.
* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_prodLift_of_exists_covering`: the same, for
  a family indexed by `Fin m`.
* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_equalizerLift_of_exists_covering`:
  condition (4) of Stacks 0GN4 from a condition on morphisms of the site.

## Implementation notes

Everything rests on Yoneda's lemma for sheaves, `CategoryTheory.Sheaf.sectionEquiv`: a section of
a sheaf `F` over `Y` is a morphism `h_Y^# ⟶ F`, so the sectionwise criterion for surjectivity out
of a coproduct becomes a statement about morphisms out of sheafified representables, and no
description of the sections of a product or of an equalizer of sheaves is ever needed. The two
sides of each required identity of sections are compared as morphisms and only then transported to
sections, by `CategoryTheory.Sheaf.sectionEquiv_comp` and
`CategoryTheory.Sheaf.sectionEquiv_map_comp`.

The passage from a morphism of sheafified representables to a morphism of the site is local in
both directions, and both directions come from the sheafification map `h_X ⟶ h_X^#` being locally
bijective: local surjectivity gives `CategoryTheory.Presheaf.imageSieve_mem` and hence
`exists_covering_sheafifiedYoneda_map_eq`, local injectivity gives
`CategoryTheory.Presheaf.equalizerSieve_mem` and hence
`exists_covering_comp_eq_of_sheafifiedYoneda_map_eq`, which is what turns the equalizer condition
on sections into the strict equation `α ≫ a = α ≫ b` in the site.

Composing two layers of coverings is `CategoryTheory.GrothendieckTopology.bind_covering`, isolated
as `exists_covering_of_comp` so that the two main proofs read as a single pass.

The index type of the two families is unconstrained — `Fin m` in the criterion that consumes
them — so the coproduct may sit at a smaller universe than the sheaves; the sectionwise criterion
for surjectivity out of a coproduct is therefore re-proved here in the direction needed, which
uses nothing but the cancellation `Sigma.ι ≫ Sigma.desc`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### Joint surjectivity out of a coproduct at an arbitrary index type -/

/-- **Joint surjectivity from local liftings.** A family `(f_i : G_i ⟶ F)` of morphisms of sheaves
of sets induces a surjection `∐_i G_i ⟶ F` as soon as every section of `F` lies, locally, in the
image of a single `f_i`.

This is the direction of `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff` that uses
nothing but the cancellation `Sigma.ι ≫ Sigma.desc`, stated for an index type in an arbitrary
universe so that it applies at `Fin m`. -/
@[sga "3 IV 4.4.8" "partial"]
theorem isLocallySurjective_sigmaDesc_of_exists_section {ι : Type*}
    {G : ι → Sheaf J (Type max u v)} {F : Sheaf J (Type max u v)} [HasCoproduct G]
    (f : ∀ i, G i ⟶ F)
    (h : ∀ ⦃U : C⦄ (s : F.obj.obj (op U)), ∃ T : Sieve U, T ∈ J U ∧
      ∀ ⦃V : C⦄ (g : V ⟶ U), T.arrows g →
        ∃ (i : ι) (t : (G i).obj.obj (op V)),
          (f i).hom.app (op V) t = F.obj.map g.op s) :
    IsLocallySurjective (Sigma.desc f) := by
  constructor
  intro U s
  obtain ⟨T, hT, hcov⟩ := h s
  refine J.superset_covering ?_ hT
  intro V g hg
  obtain ⟨i, t, ht⟩ := hcov g hg
  refine ⟨(Sigma.ι G i).hom.app (op V) t, ?_⟩
  rw [← ht, ← NatTrans.comp_app_apply, ← ObjectProperty.FullSubcategory.comp_hom, Sigma.ι_desc]

/-! ### Composing two layers of coverings -/

/-- **Two layers of coverings compose.** If a covering sieve of `X` has, over each of its members
`f`, a covering sieve whose members `g` all satisfy `P (g ≫ f)`, then `X` carries a covering sieve
all of whose members satisfy `P`. -/
theorem exists_covering_of_comp {X : C} (P : ∀ ⦃Z : C⦄, (Z ⟶ X) → Prop) {T : Sieve X}
    (hT : T ∈ J X)
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X), T.arrows f →
      ∃ R : Sieve Y, R ∈ J Y ∧ ∀ ⦃Z : C⦄ (g : Z ⟶ Y), R.arrows g → P (g ≫ f)) :
    ∃ T' : Sieve X, T' ∈ J X ∧ ∀ ⦃Z : C⦄ (g : Z ⟶ X), T'.arrows g → P g := by
  choose R hR hP using fun (Y : C) (f : Y ⟶ X) (hf : T.arrows f) => h f hf
  refine ⟨Sieve.bind T.arrows (fun {Y} {f} hf => R Y f hf),
    J.bind_covering hT (fun {Y} {f} hf => hR Y f hf), ?_⟩
  rintro Z g ⟨Y, g', f, hf, hg', rfl⟩
  exact hP Y f hf g' hg'

/-! ### Morphisms of sheafified representables, locally -/

/-- **A morphism of sheafified representables is locally a morphism of the site.** For every
`σ : h_Y^# ⟶ h_X^#` there is a covering sieve of `Y` over each of whose members `g` the composite
`h_g^# ≫ σ` is the sheafified representable of a morphism of the site.

The sheafification map `h_X ⟶ h_X^#` is locally surjective, so the sieve of local liftings of the
section of `h_X^#` that `σ` names is covering; a lifting over `g` is literally a morphism
`Z ⟶ X`. -/
theorem exists_covering_sheafifiedYoneda_map_eq {X Y : C}
    (σ : (sheafifiedYoneda J).obj Y ⟶ (sheafifiedYoneda J).obj X) :
    ∃ T : Sieve Y, T ∈ J Y ∧ ∀ ⦃Z : C⦄ (g : Z ⟶ Y), T.arrows g →
      ∃ α : Z ⟶ X, (sheafifiedYoneda J).map g ≫ σ = (sheafifiedYoneda J).map α := by
  refine ⟨Presheaf.imageSieve (toSheafify J (uliftYoneda.{u}.obj X)) (sectionEquiv J σ),
    Presheaf.imageSieve_mem J (toSheafify J (uliftYoneda.{u}.obj X)) (sectionEquiv J σ), ?_⟩
  intro Z g hg
  obtain ⟨⟨α⟩, ht⟩ := hg
  refine ⟨α, (sectionEquiv J).injective ?_⟩
  rw [sectionEquiv_map_comp, sectionEquiv_sheafifiedYoneda_map]
  exact ht.symm

/-- **Two morphisms of the site with equal sheafified representables agree locally.** The
sheafification map `h_X ⟶ h_X^#` is locally injective, so the sieve on which the two sections it
sends `a` and `b` to agree is covering, and a member of that sieve is a morphism `g` with
`g ≫ a = g ≫ b`. -/
theorem exists_covering_comp_eq_of_sheafifiedYoneda_map_eq {X Y : C} (a b : Y ⟶ X)
    (hab : (sheafifiedYoneda J).map a = (sheafifiedYoneda J).map b) :
    ∃ T : Sieve Y, T ∈ J Y ∧ ∀ ⦃Z : C⦄ (g : Z ⟶ Y), T.arrows g → g ≫ a = g ≫ b := by
  have hsec : (toSheafify J (uliftYoneda.{u}.obj X)).app (op Y) (ULift.up a) =
      (toSheafify J (uliftYoneda.{u}.obj X)).app (op Y) (ULift.up b) := by
    rw [← sectionEquiv_sheafifiedYoneda_map, ← sectionEquiv_sheafifiedYoneda_map, hab]
  refine ⟨Presheaf.equalizerSieve (F := uliftYoneda.{u}.obj X) (X := op Y)
      (ULift.up a) (ULift.up b),
    Presheaf.equalizerSieve_mem J (toSheafify J (uliftYoneda.{u}.obj X)) _ _ hsec, ?_⟩
  intro Z g hg
  have hg' : (uliftYoneda.{u}.obj X).map g.op (ULift.up a) =
      (uliftYoneda.{u}.obj X).map g.op (ULift.up b) := hg
  exact congrArg ULift.down hg'

/-- If `h_c^# ≫ L = h_g^# ≫ σ`, then `L` sends the section named by `h_c^#` to the restriction
along `g` of the section named by `σ`. -/
private theorem exists_preimage_of_map_comp_eq {F : Sheaf J (Type max u v)} {Y V W : C}
    (σ : (sheafifiedYoneda J).obj Y ⟶ F) (L : (sheafifiedYoneda J).obj V ⟶ F) (g : W ⟶ Y)
    (c : W ⟶ V) (key : (sheafifiedYoneda J).map c ≫ L = (sheafifiedYoneda J).map g ≫ σ) :
    ∃ t : ((sheafifiedYoneda J).obj V).obj.obj (op W),
      L.hom.app (op W) t = F.obj.map g.op (sectionEquiv J σ) := by
  refine ⟨sectionEquiv J ((sheafifiedYoneda J).map c), ?_⟩
  have hkey := congrArg (sectionEquiv J) key
  rwa [sectionEquiv_comp, sectionEquiv_map_comp] at hkey

/-! ### Condition (3) of Stacks 0GN4 from pairs of morphisms of the site -/

/-- **Condition (3) of Stacks 0GN4 from a condition on pairs of morphisms of the site.** Let
`p_i : V_i ⟶ X` and `q_i : V_i ⟶ X'` be a family of pairs of morphisms of the site such
that every pair `α : Y ⟶ X`, `β : Y ⟶ X'` factors, locally on `Y`, through some `(p_i, q_i)`.
Then `∐_i h_{V_i}^# ⟶ h_X^# ⨯ h_{X'}^#` is a surjection of sheaves of sets.

A section of `h_X^# ⨯ h_{X'}^#` over `Y` is a morphism `σ : h_Y^# ⟶ h_X^# ⨯ h_{X'}^#`, whose two
components are, locally on `Y`, sheafified representables of a pair of morphisms of the site by
`exists_covering_sheafifiedYoneda_map_eq`; the hypothesis then factors that pair, and the required
identity of sections is an identity of morphisms into a product.

The index type is arbitrary, the coproduct of the sheafified representables being a hypothesis;
the criterion of Stacks 0GN4 instantiates it at `Fin m`, and Stacks 0GMS case (2) at an arbitrary
finite type in the canonical sheaf universe of the site. -/
theorem isLocallySurjective_sigmaDesc_prodLift_of_exists_covering_anyIndex
    {X X' : C} {ι : Type*}
    (V : ι → C) (p : ∀ i, V i ⟶ X) (q : ∀ i, V i ⟶ X')
    [HasCoproduct fun i => (sheafifiedYoneda J).obj (V i)]
    (h : ∀ (Y : C) (α : Y ⟶ X) (β : Y ⟶ X'), ∃ T : Sieve Y, T ∈ J Y ∧
      ∀ ⦃Z : C⦄ (g : Z ⟶ Y), T.arrows g →
        ∃ (i : ι) (r : Z ⟶ V i), r ≫ p i = g ≫ α ∧ r ≫ q i = g ≫ β) :
    IsLocallySurjective (Sigma.desc fun i =>
      prod.lift ((sheafifiedYoneda J).map (p i)) ((sheafifiedYoneda J).map (q i))) := by
  let Pr := (sheafifiedYoneda J).obj X ⨯ (sheafifiedYoneda J).obj X'
  let L : ∀ i, (sheafifiedYoneda J).obj (V i) ⟶ Pr := fun i =>
    prod.lift ((sheafifiedYoneda J).map (p i)) ((sheafifiedYoneda J).map (q i))
  show IsLocallySurjective (Sigma.desc L)
  refine isLocallySurjective_sigmaDesc_of_exists_section L ?_
  intro Y s
  obtain ⟨σ, rfl⟩ := (sectionEquiv J).surjective s
  have hσlift : prod.lift (σ ≫ prod.fst) (σ ≫ prod.snd) = σ := by
    rw [← prod.comp_lift, prod.lift_fst_snd, Category.comp_id]
  obtain ⟨T₁, hT₁, h₁⟩ := exists_covering_sheafifiedYoneda_map_eq (σ ≫ prod.fst)
  obtain ⟨T₂, hT₂, h₂⟩ := exists_covering_sheafifiedYoneda_map_eq (σ ≫ prod.snd)
  refine exists_covering_of_comp
    (P := fun ⦃Z : C⦄ (g : Z ⟶ Y) => ∃ (i : ι)
      (t : ((sheafifiedYoneda J).obj (V i)).obj.obj (op Z)),
      (L i).hom.app (op Z) t = Pr.obj.map g.op (sectionEquiv J σ))
    (J.intersection_covering hT₁ hT₂) ?_
  intro Z g hg
  obtain ⟨α, hα⟩ := h₁ g hg.1
  obtain ⟨β, hβ⟩ := h₂ g hg.2
  obtain ⟨T₃, hT₃, h₃⟩ := h Z α β
  refine ⟨T₃, hT₃, ?_⟩
  intro W r hr
  obtain ⟨i, c, hc₁, hc₂⟩ := h₃ r hr
  exact ⟨i, exists_preimage_of_map_comp_eq σ (L i) (r ≫ g) c <|
    calc (sheafifiedYoneda J).map c ≫ L i
        = prod.lift ((sheafifiedYoneda J).map (c ≫ p i))
            ((sheafifiedYoneda J).map (c ≫ q i)) := by
          simp only [L, prod.comp_lift, Functor.map_comp]
      _ = prod.lift ((sheafifiedYoneda J).map (r ≫ α))
            ((sheafifiedYoneda J).map (r ≫ β)) := by rw [hc₁, hc₂]
      _ = (sheafifiedYoneda J).map r ≫ prod.lift ((sheafifiedYoneda J).map g ≫ σ ≫ prod.fst)
            ((sheafifiedYoneda J).map g ≫ σ ≫ prod.snd) := by
          rw [prod.comp_lift, hα, hβ, Functor.map_comp, Functor.map_comp]
      _ = (sheafifiedYoneda J).map (r ≫ g) ≫ σ := by
          rw [← prod.comp_lift, hσlift, Functor.map_comp, Category.assoc]⟩

/-- **Condition (3) of Stacks 0GN4 from a condition on pairs of morphisms of the site.** Let
`p_i : V_i ⟶ X` and `q_i : V_i ⟶ X'` be a finite family of pairs of morphisms of the site such
that every pair `α : Y ⟶ X`, `β : Y ⟶ X'` factors, locally on `Y`, through some `(p_i, q_i)`.
Then `∐_i h_{V_i}^# ⟶ h_X^# ⨯ h_{X'}^#` is a surjection of sheaves of sets.

This is the `Fin m`-indexed instance of
`isLocallySurjective_sigmaDesc_prodLift_of_exists_covering_anyIndex`, in the shape the criterion
of Stacks 0GN4 consumes it. -/
theorem isLocallySurjective_sigmaDesc_prodLift_of_exists_covering {X X' : C} {m : ℕ}
    (V : Fin m → C) (p : ∀ i, V i ⟶ X) (q : ∀ i, V i ⟶ X')
    [HasCoproduct fun i => (sheafifiedYoneda J).obj (V i)]
    (h : ∀ (Y : C) (α : Y ⟶ X) (β : Y ⟶ X'), ∃ T : Sieve Y, T ∈ J Y ∧
      ∀ ⦃Z : C⦄ (g : Z ⟶ Y), T.arrows g →
        ∃ (i : Fin m) (r : Z ⟶ V i), r ≫ p i = g ≫ α ∧ r ≫ q i = g ≫ β) :
    IsLocallySurjective (Sigma.desc fun i =>
      prod.lift ((sheafifiedYoneda J).map (p i)) ((sheafifiedYoneda J).map (q i))) :=
  isLocallySurjective_sigmaDesc_prodLift_of_exists_covering_anyIndex V p q h

/-! ### Condition (4) of Stacks 0GN4 from morphisms of the site -/

/-- **Condition (4) of Stacks 0GN4 from a condition on morphisms of the site.** Let `a, b : X ⟶ X'`
be two morphisms of the site and let `p_i : V_i ⟶ X` be a finite family equalizing them such that
every `α : Y ⟶ X` with `α ≫ a = α ≫ b` factors, locally on `Y`, through some `p_i`. Then
`∐_i h_{V_i}^# ⟶ Equalizer(h_a^#, h_b^#)` is a surjection of sheaves of sets.

A section of the equalizer over `Y` is a morphism `h_Y^# ⟶ Equalizer(h_a^#, h_b^#)`, which the
equalizer inclusion turns into a `σ : h_Y^# ⟶ h_X^#` with `σ ≫ h_a^# = σ ≫ h_b^#`. Locally `σ` is
`h_α^#` for a morphism `α` of the site, and then `h_{α ≫ a}^# = h_{α ≫ b}^#`, so a further
covering makes `α ≫ a = α ≫ b` hold in the site itself, which is what the hypothesis asks for. The
required identity of sections is an identity of morphisms into the equalizer, and the equalizer
inclusion is a monomorphism. -/
theorem isLocallySurjective_sigmaDesc_equalizerLift_of_exists_covering {X X' : C} (a b : X ⟶ X')
    {m : ℕ} (V : Fin m → C) (p : ∀ i, V i ⟶ X) (hp : ∀ i, p i ≫ a = p i ≫ b)
    [HasCoproduct fun i => (sheafifiedYoneda J).obj (V i)]
    (h : ∀ (Y : C) (α : Y ⟶ X), α ≫ a = α ≫ b → ∃ T : Sieve Y, T ∈ J Y ∧
      ∀ ⦃Z : C⦄ (g : Z ⟶ Y), T.arrows g → ∃ (i : Fin m) (r : Z ⟶ V i), r ≫ p i = g ≫ α) :
    IsLocallySurjective (Sigma.desc fun i =>
      equalizer.lift (f := (sheafifiedYoneda J).map a) (g := (sheafifiedYoneda J).map b)
        ((sheafifiedYoneda J).map (p i)) (by
          simpa only [Functor.map_comp] using congrArg (sheafifiedYoneda J).map (hp i))) := by
  let E := equalizer ((sheafifiedYoneda J).map a) ((sheafifiedYoneda J).map b)
  let ι : E ⟶ (sheafifiedYoneda J).obj X :=
    equalizer.ι ((sheafifiedYoneda J).map a) ((sheafifiedYoneda J).map b)
  let L : ∀ i, (sheafifiedYoneda J).obj (V i) ⟶ E := fun i =>
    equalizer.lift (f := (sheafifiedYoneda J).map a) (g := (sheafifiedYoneda J).map b)
      ((sheafifiedYoneda J).map (p i)) (by
        simpa only [Functor.map_comp] using congrArg (sheafifiedYoneda J).map (hp i))
  have hLι : ∀ i, L i ≫ ι = (sheafifiedYoneda J).map (p i) := fun i => equalizer.lift_ι _ _
  have hιmono : Mono ι := equalizer.ι_mono
  show IsLocallySurjective (Sigma.desc L)
  refine isLocallySurjective_sigmaDesc_of_exists_section L ?_
  intro Y s
  obtain ⟨τ, rfl⟩ := (sectionEquiv J).surjective s
  have hcond : (τ ≫ ι) ≫ (sheafifiedYoneda J).map a = (τ ≫ ι) ≫ (sheafifiedYoneda J).map b := by
    rw [Category.assoc, Category.assoc, equalizer.condition]
  obtain ⟨T₁, hT₁, h₁⟩ := exists_covering_sheafifiedYoneda_map_eq (τ ≫ ι)
  refine exists_covering_of_comp
    (P := fun ⦃Z : C⦄ (g : Z ⟶ Y) => ∃ (i : Fin m)
      (t : ((sheafifiedYoneda J).obj (V i)).obj.obj (op Z)),
      (L i).hom.app (op Z) t = E.obj.map g.op (sectionEquiv J τ)) hT₁ ?_
  intro Z g hg
  obtain ⟨α, hα⟩ := h₁ g hg
  have hmap : (sheafifiedYoneda J).map (α ≫ a) = (sheafifiedYoneda J).map (α ≫ b) := by
    rw [Functor.map_comp, Functor.map_comp, ← hα]
    simpa only [Category.assoc] using whisker_eq ((sheafifiedYoneda J).map g) hcond
  obtain ⟨T₂, hT₂, h₂⟩ := exists_covering_comp_eq_of_sheafifiedYoneda_map_eq (α ≫ a) (α ≫ b) hmap
  refine exists_covering_of_comp
    (P := fun ⦃W : C⦄ (r : W ⟶ Z) => ∃ (i : Fin m)
      (t : ((sheafifiedYoneda J).obj (V i)).obj.obj (op W)),
      (L i).hom.app (op W) t = E.obj.map (r ≫ g).op (sectionEquiv J τ)) hT₂ ?_
  intro W r hr
  have hreq : (r ≫ α) ≫ a = (r ≫ α) ≫ b := by simpa only [Category.assoc] using h₂ r hr
  obtain ⟨T₃, hT₃, h₃⟩ := h W (r ≫ α) hreq
  refine ⟨T₃, hT₃, ?_⟩
  intro W' c hc
  obtain ⟨i, d, hd⟩ := h₃ c hc
  refine ⟨i, exists_preimage_of_map_comp_eq τ (L i) ((c ≫ r) ≫ g) d ?_⟩
  refine (cancel_mono ι).1 ?_
  calc ((sheafifiedYoneda J).map d ≫ L i) ≫ ι
      = (sheafifiedYoneda J).map (d ≫ p i) := by
        rw [Category.assoc, hLι, ← Functor.map_comp]
    _ = (sheafifiedYoneda J).map (c ≫ r ≫ α) := by rw [hd]
    _ = (sheafifiedYoneda J).map c ≫ (sheafifiedYoneda J).map r ≫
          ((sheafifiedYoneda J).map g ≫ τ ≫ ι) := by
        rw [hα, Functor.map_comp, Functor.map_comp]
    _ = ((sheafifiedYoneda J).map ((c ≫ r) ≫ g) ≫ τ) ≫ ι := by
        simp only [Functor.map_comp, Category.assoc]

end CategoryTheory.Sheaf

end
