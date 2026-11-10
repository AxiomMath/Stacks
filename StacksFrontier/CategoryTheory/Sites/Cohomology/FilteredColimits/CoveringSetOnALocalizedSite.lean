module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A covering set of quasi-compact sheaves on a localized site

Stacks 0GN3 puts five hypotheses on a set `S` of sheaves of sets on a site `C`:

1. some `K ∈ S` surjects onto the final sheaf;
2. a surjection `G ⟶ K` onto a member of `S` admits a map `K' ⟶ G` from a member of `S` whose
   composite `K' ⟶ K` is still surjective;
3. two members of `S` admit a surjection onto their product from a member of `S`;
4. two parallel morphisms between members of `S` admit a surjection onto their equalizer from a
   member of `S`;
5. every member of `S` is quasi-compact (Stacks 0D07).

The proof of Stacks 0GN3 is an induction on the cohomological degree, and its inductive step is
applied not to `C` itself but to the localized sites `C/Kⁿ` for `K ∈ S`. So the induction only
runs if those sites again carry a set with properties (1)–(5). This file supplies that: it
constructs, for `K ∈ S` and `n : ℕ`, a set of sheaves of sets on `C/Kⁿ` satisfying (1)–(5).

The set is constructed in the slice `Sh(C)/Kⁿ`: it consists of the objects `K' ⟶ Kⁿ` with `K' ∈ S`.
Property (2) there is property (2) here, since epimorphisms of a slice are the epimorphisms of the
underlying sheaves. Property (1) needs `Kⁿ` to be covered by a member of `S`, which follows from
(1) and (3) by induction on `n`. Property (3) in the slice is a fibre product over `Kⁿ`, hence an
equalizer of two maps out of a binary product, so it reduces to (3) and (4). Property (4) in the
slice is (4). Property (5) is quasi-compactness, which transports across the equivalence
`Sh(C/Kⁿ) ≌ Sh(C)/Kⁿ` of Stacks 0791 because the forgetful functor of a slice preserves small
coproducts and epimorphisms and reflects epimorphisms.

## Main definitions

* `Stacks.Cohomology.CoveringSet.sheafPower`: the `n`-fold self product of a sheaf of sets.

## Main results

* `Stacks.Cohomology.CoveringSet.exists_S_cover_of_sheafPower`: hypotheses (1) and (3) cover
  every self power of a member of `S` by a member of `S`.
* `Stacks.Cohomology.CoveringSet.covering_properties_equivalence`: properties (1)–(4), in
  epimorphism form, transport along an equivalence of finitely complete categories.
* `Stacks.Cohomology.CoveringSet.isQuasiCompact_of_slice_equivalence`: quasi-compactness
  transports back along an equivalence with a slice.
* `Stacks.Cohomology.CoveringSet.exists_localized_coveringSet`: the site localized at a self
  power of a member of `S` again carries a set satisfying (1)–(5).

## Implementation notes

Surjectivity of a map of sheaves of sets is `CategoryTheory.Sheaf.IsLocallySurjective` (Stacks
00WM (2)) and quasi-compactness is `CategoryTheory.Sheaf.IsQuasiCompact` (Stacks 0D07).

Inside the slice the hypotheses are stated with epimorphisms rather than with local surjectivity,
since the slice objects are not sheaves; `covering_properties_equivalence` is stated for
epimorphisms in an arbitrary finitely complete category, and the two notions agree for maps of
sheaves by `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`.

The localized site is the costructured-arrow category of the Yoneda embedding over the
underlying presheaf of `Kⁿ` with its restricted topology, and the equivalence with the slice is
`CategoryTheory.Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda`.

The site and the coefficients live in one universe `u`.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 0D07](https://stacks.math.columbia.edu/tag/0D07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.CoveringSet
/-- Two sections of a binary product of sheaves of sets over the same object of the site agree
as soon as their two projections agree. -/
private lemma prod_section_ext {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (X Y : Sheaf J (Type u)) (W : Cᵒᵖ)
    {x y : (X ⨯ Y).obj.obj W}
    (h₁ : (Limits.prod.fst : X ⨯ Y ⟶ X).hom.app W x =
      (Limits.prod.fst : X ⨯ Y ⟶ X).hom.app W y)
    (h₂ : (Limits.prod.snd : X ⨯ Y ⟶ Y).hom.app W x =
      (Limits.prod.snd : X ⨯ Y ⟶ Y).hom.app W y) : x = y := by
  let G := sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj W
  let hlim := isLimitOfHasBinaryProductOfPreservesLimit G X Y
  let f : PUnit.{u + 1} ⟶ G.obj (X ⨯ Y) := ↾fun _ => x
  let g : PUnit.{u + 1} ⟶ G.obj (X ⨯ Y) := ↾fun _ => y
  have hf : f ≫ G.map (Limits.prod.fst : X ⨯ Y ⟶ X) =
      g ≫ G.map (Limits.prod.fst : X ⨯ Y ⟶ X) := ConcreteCategory.hom_ext _ _ fun _ => h₁
  have hg : f ≫ G.map (Limits.prod.snd : X ⨯ Y ⟶ Y) =
      g ≫ G.map (Limits.prod.snd : X ⨯ Y ⟶ Y) := ConcreteCategory.hom_ext _ _ fun _ => h₂
  exact congrArg (fun k => k PUnit.unit) (BinaryFan.IsLimit.hom_ext hlim hf hg)

/-- Multiplying a locally surjective map of sheaves of sets by the identity of a third sheaf
leaves it locally surjective. -/
public lemma isLocallySurjective_prod_map_right {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {X Z W : Sheaf J (Type u)}
    (g : Z ⟶ W) (hg : Sheaf.IsLocallySurjective g) :
    Sheaf.IsLocallySurjective (prod.map (𝟙 X) g) := by
  constructor
  intro U z
  let x := (Limits.prod.fst : X ⨯ W ⟶ X).hom.app (Opposite.op U) z
  let y := (Limits.prod.snd : X ⨯ W ⟶ W).hom.app (Opposite.op U) z
  have hy : Presheaf.imageSieve g.hom y ∈ J U := hg.imageSieve_mem y
  apply J.superset_covering (fun V f hf => ?_) hy
  obtain ⟨y', hy'⟩ := hf
  obtain ⟨z', hz₁, hz₂⟩ := Sheaf.exists_section_of_prod X Z (Opposite.op V)
    (X.obj.map f.op x) y'
  refine ⟨z', ?_⟩
  apply prod_section_ext J X W (Opposite.op V)
  · change (prod.map (𝟙 X) g ≫ prod.fst).hom.app _ z' = _
    rw [prod.map_fst, Category.comp_id, hz₁]
    exact (NatTrans.naturality_apply _ f.op z).symm
  · change (prod.map (𝟙 X) g ≫ prod.snd).hom.app _ z' = _
    rw [prod.map_snd]
    change g.hom.app _ ((prod.snd : X ⨯ Z ⟶ Z).hom.app _ z') = _
    rw [hz₂, hy']
    exact (NatTrans.naturality_apply _ f.op z).symm

/-- A map `q : P ⟶ Y` of sheaves of sets is locally surjective as soon as there are a locally
surjective `e : X ⟶ Z` and a map `g : Y ⟶ Z` such that every commutative square from a sheaf `T`
over `e` and `g` factors through `q`. -/
public lemma isLocallySurjective_of_exists_lift {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) {P X Y Z : Sheaf J (Type u)}
    (q : P ⟶ Y) (e : X ⟶ Z) (g : Y ⟶ Z) (he : Sheaf.IsLocallySurjective e)
    (h : ∀ (T : Sheaf J (Type u)) (a : T ⟶ X) (b : T ⟶ Y),
      a ≫ e = b ≫ g → ∃ c : T ⟶ P, c ≫ q = b) :
    Sheaf.IsLocallySurjective q := by
  constructor
  intro U y
  apply J.superset_covering (fun V f hf => ?_) (he.imageSieve_mem (g.hom.app (op U) y))
  obtain ⟨x, hx⟩ := hf
  rw [← g.hom.naturality_apply f.op y] at hx
  have heq : (Sheaf.sectionEquiv J).symm x ≫ e =
      (Sheaf.sectionEquiv J).symm (Y.obj.map f.op y) ≫ g := by
    rw [← Sheaf.sectionEquiv_symm_comp, ← Sheaf.sectionEquiv_symm_comp, hx]
  obtain ⟨c, hc⟩ := h _ _ _ heq
  refine ⟨Sheaf.sectionEquiv J c, ?_⟩
  rw [← Sheaf.sectionEquiv_comp, hc, Equiv.apply_symm_apply]

/-- If equalizers of pairs of maps from members of `S` into `X` and into `Y` are covered by
members of `S`, then so are equalizers of pairs of maps into `X ⨯ Y`. -/
private lemma exists_cover_equalizer_prod {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    {X Y : Sheaf J (Type u)}
    (hX : ∀ {A : Sheaf J (Type u)} (a b : A ⟶ X), A ∈ S →
      ∃ Q ∈ S, ∃ q : Q ⟶ equalizer a b, Sheaf.IsLocallySurjective q)
    (hY : ∀ {A : Sheaf J (Type u)} (a b : A ⟶ Y), A ∈ S →
      ∃ Q ∈ S, ∃ q : Q ⟶ equalizer a b, Sheaf.IsLocallySurjective q)
    {A : Sheaf J (Type u)} (a b : A ⟶ X ⨯ Y) (hA : A ∈ S) :
    ∃ Q ∈ S, ∃ q : Q ⟶ equalizer a b, Sheaf.IsLocallySurjective q := by
  let aX := a ≫ prod.fst
  let bX := b ≫ prod.fst
  obtain ⟨P, hP, e, he⟩ := hX aX bX hA
  let r : P ⟶ A := e ≫ equalizer.ι aX bX
  let aY := r ≫ a ≫ prod.snd
  let bY := r ≫ b ≫ prod.snd
  obtain ⟨Q, hQ, d, hd⟩ := hY aY bY hP
  have hr : r ≫ aX = r ≫ bX := by
    dsimp [r]
    rw [Category.assoc, Category.assoc, equalizer.condition]
  have hq : (equalizer.ι aY bY ≫ r) ≫ a =
      (equalizer.ι aY bY ≫ r) ≫ b := by
    apply prod.hom_ext
    · simpa only [Category.assoc] using congrArg (fun z => equalizer.ι aY bY ≫ z) hr
    · simpa only [Category.assoc] using equalizer.condition aY bY
  let q : equalizer aY bY ⟶ equalizer a b :=
    equalizer.lift (equalizer.ι aY bY ≫ r) hq
  let t : equalizer a b ⟶ equalizer aX bX :=
    equalizer.lift (equalizer.ι a b)
      (by simpa only [Category.assoc] using
        congrArg (fun z => z ≫ prod.fst) (equalizer.condition a b))
  have hqs : Sheaf.IsLocallySurjective q := by
    apply isLocallySurjective_of_exists_lift J q e t he
    intro T c v hcv
    have hcr : c ≫ r = v ≫ equalizer.ι a b := by
      dsimp [r]
      rw [← Category.assoc, hcv, Category.assoc]
      simp only [t, equalizer.lift_ι]
    have hc : c ≫ aY = c ≫ bY := by
      calc
        c ≫ aY = (c ≫ r) ≫ (a ≫ prod.snd) := by simp [aY]
        _ = (v ≫ equalizer.ι a b) ≫ (a ≫ prod.snd) := by rw [hcr]
        _ = (v ≫ equalizer.ι a b) ≫ (b ≫ prod.snd) := by
          simpa only [Category.assoc] using
            congrArg (fun z => v ≫ z ≫ prod.snd) (equalizer.condition a b)
        _ = c ≫ bY := by rw [← hcr]; simp [bY]
    refine ⟨equalizer.lift c hc, ?_⟩
    apply equalizer.hom_ext
    simp only [Category.assoc, q, equalizer.lift_ι, equalizer.lift_ι_assoc]
    exact hcr
  exact ⟨Q, hQ, d ≫ q, Sheaf.isLocallySurjective_comp d q⟩

/-- The `n`-fold self product `Kⁿ` of a sheaf of sets, with `K⁰` the final sheaf. -/
public noncomputable def sheafPower {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (K : Sheaf J (Type u)) (n : ℕ) : Sheaf J (Type u) :=
  Nat.rec (motive := fun _ => Sheaf J (Type u)) (⊤_ (Sheaf J (Type u)))
    (fun _ X => K ⨯ X) n

/-- `Kⁿ⁺¹` is `K ⨯ Kⁿ`, by construction. -/
public lemma sheafPower_succ {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (K : Sheaf J (Type u)) (n : ℕ) :
    sheafPower J K (n + 1) = (K ⨯ sheafPower J K n) := rfl

/-- Hypotheses (1) and (3) of Stacks 0GN3 make every self power `Kⁿ` of a member of `S` the
target of a locally surjective map from a member of `S`. -/
public lemma exists_S_cover_of_sheafPower {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    {K : Sheaf J (Type u)} (hK : K ∈ S) (n : ℕ) :
    ∃ K' ∈ S, ∃ f : K' ⟶ sheafPower J K n, Sheaf.IsLocallySurjective f := by
  induction n with
  | zero =>
      obtain ⟨K', hK'S, hK'⟩ := h_terminal
      exact ⟨K', hK'S, terminal.from K', by simpa [sheafPower] using hK'⟩
  | succ n ih =>
      obtain ⟨K', hK'S, q, hq⟩ := ih
      obtain ⟨P, hPS, e, he⟩ := h_product K hK K' hK'S
      have := isLocallySurjective_prod_map_right J (X := K) q hq
      exact ⟨P, hPS, e ≫ prod.map (𝟙 K) q, Sheaf.isLocallySurjective_comp e (prod.map (𝟙 K) q)⟩

/-- A fibre product of two members of `S` over a sheaf `T` all of whose equalizers of maps from
members of `S` are covered by members of `S` is itself covered by a member of `S`: the fibre
product is the equalizer of the two composites out of the binary product. -/
private lemma exists_S_cover_of_pullback {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    {T : Sheaf J (Type u)}
    (h_equalizer : ∀ {K : Sheaf J (Type u)} (a b : K ⟶ T), K ∈ S →
      ∃ K'' ∈ S, ∃ f : K'' ⟶ equalizer a b, Sheaf.IsLocallySurjective f)
    {A B : Sheaf J (Type u)} (hA : A ∈ S) (hB : B ∈ S)
    (f : A ⟶ T) (g : B ⟶ T) :
    ∃ Q ∈ S, ∃ q : Q ⟶ pullback f g, Sheaf.IsLocallySurjective q := by
  obtain ⟨P, hP, e, he⟩ := h_product A hA B hB
  let m : pullback f g ⟶ A ⨯ B :=
    prod.lift (pullback.fst f g) (pullback.snd f g)
  let a : P ⟶ T := e ≫ prod.fst ≫ f
  let b : P ⟶ T := e ≫ prod.snd ≫ g
  let j : equalizer a b ⟶ pullback f g :=
    pullback.lift (equalizer.ι a b ≫ e ≫ prod.fst)
      (equalizer.ι a b ≫ e ≫ prod.snd)
      (by simpa only [Category.assoc] using equalizer.condition a b)
  have hj : Sheaf.IsLocallySurjective j := by
    apply isLocallySurjective_of_exists_lift J j e m he
    intro W c v hcv
    have hc : c ≫ a = c ≫ b := by
      calc
        c ≫ a = (c ≫ e) ≫ prod.fst ≫ f := by simp [a]
        _ = (v ≫ m) ≫ prod.fst ≫ f := by rw [hcv]
        _ = v ≫ (pullback.fst f g ≫ f) := by simp [m]
        _ = v ≫ (pullback.snd f g ≫ g) := by rw [pullback.condition]
        _ = (v ≫ m) ≫ prod.snd ≫ g := by simp [m]
        _ = (c ≫ e) ≫ prod.snd ≫ g := by rw [hcv]
        _ = c ≫ b := by simp [b]
    refine ⟨equalizer.lift c hc, ?_⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, j, pullback.lift_fst, equalizer.lift_ι_assoc]
      simpa only [Category.assoc, m, prod.lift_fst] using
        congrArg (fun z => z ≫ prod.fst) hcv
    · simp only [Category.assoc, j, pullback.lift_snd, equalizer.lift_ι_assoc]
      simpa only [Category.assoc, m, prod.lift_snd] using
        congrArg (fun z => z ≫ prod.snd) hcv
  obtain ⟨Q, hQ, q, hq⟩ := h_equalizer a b hP
  exact ⟨Q, hQ, q ≫ j, Sheaf.isLocallySurjective_comp q j⟩

/-- Equalizers of pairs of maps from a member of `S` into a self power `Kⁿ` are covered by
members of `S`, by induction on `n` from hypothesis (4). -/
private lemma exists_S_cover_equalizer_sheafPower {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    (h_equalizer : ∀ {A B : Sheaf J (Type u)} (a b : A ⟶ B), A ∈ S → B ∈ S →
      ∃ Q ∈ S, ∃ q : Q ⟶ equalizer a b, Sheaf.IsLocallySurjective q)
    {K : Sheaf J (Type u)} (hK : K ∈ S) (n : ℕ)
    {A : Sheaf J (Type u)} (a b : A ⟶ sheafPower J K n) (hA : A ∈ S) :
    ∃ Q ∈ S, ∃ q : Q ⟶ equalizer a b, Sheaf.IsLocallySurjective q := by
  induction n generalizing A with
  | zero =>
      have hab : a = b := terminalIsTerminal.hom_ext a b
      subst b
      exact ⟨A, hA, (equalizer.isoSourceOfSelf a).inv,
        (Sheaf.isLocallySurjective_iff_epi _).2 inferInstance⟩
  | succ n ih =>
      exact exists_cover_equalizer_prod J S
        (fun f g hB => h_equalizer f g hB hK) (fun f g hB => ih f g hB) a b hA

/-- Fibre products of two members of `S` over a self power `Kⁿ` are covered by members of `S`. -/
private lemma exists_S_cover_pullback_sheafPower {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_equalizer : ∀ {A B : Sheaf J (Type u)} (a b : A ⟶ B), A ∈ S → B ∈ S →
      ∃ Q ∈ S, ∃ q : Q ⟶ equalizer a b, Sheaf.IsLocallySurjective q)
    {K : Sheaf J (Type u)} (hK : K ∈ S) (n : ℕ)
    {A B : Sheaf J (Type u)} (hA : A ∈ S) (hB : B ∈ S)
    (a : A ⟶ sheafPower J K n) (b : B ⟶ sheafPower J K n) :
    ∃ Q ∈ S, ∃ q : Q ⟶ pullback a b, Sheaf.IsLocallySurjective q :=
  exists_S_cover_of_pullback J S h_product
    (fun f g hP => exists_S_cover_equalizer_sheafPower J S h_equalizer hK n f g hP)
    hA hB a b

/-- A member of `S` mapping locally surjectively to `T` is, viewed in the slice over `T`, an
object whose map to the final object of the slice is epimorphic. -/
private lemma exists_S_over_cover_terminal {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    {T : Sheaf J (Type u)}
    (hT : ∃ Q ∈ S, ∃ q : Q ⟶ T, Sheaf.IsLocallySurjective q) :
    ∃ Q : Over T, Q.left ∈ S ∧ Epi (terminal.from Q) := by
  obtain ⟨Q, hQ, q, hq⟩ := hT
  have : Epi q := (Sheaf.isLocallySurjective_iff_epi q).1 hq
  let R : Over T := Over.mk q
  let t : R ⟶ Over.mk (𝟙 T) := Over.homMk q
  have : Epi t := by dsimp [t]; infer_instance
  have ht : IsTerminal (Over.mk (𝟙 T)) := Over.mkIdTerminal
  have hfac : t ≫ (terminalIsoIsTerminal ht).inv = terminal.from R :=
    terminal.hom_ext _ _
  exact ⟨R, hQ, by rw [← hfac]; infer_instance⟩

/-- Property (2) of Stacks 0GN3 for the objects of the slice over `T` whose source lies in `S`,
deduced from property (2) for `S`. -/
private lemma exists_S_over_lift {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    {T : Sheaf J (Type u)} {G K : Over T}
    (f : G ⟶ K) (hK : K.left ∈ S) (hf : Epi f) :
    ∃ Q : Over T, Q.left ∈ S ∧ ∃ g : Q ⟶ G, Epi (g ≫ f) := by
  have : Epi f.left := (Over.epi_iff_epi_left f).1 hf
  obtain ⟨Q, hQ, q, hq⟩ := h_lift f.left hK
    ((Sheaf.isLocallySurjective_iff_epi _).2 inferInstance)
  have : Epi (q ≫ f.left) := (Sheaf.isLocallySurjective_iff_epi _).1 hq
  let Q' : Over T := Over.mk (q ≫ G.hom)
  let g : Q' ⟶ G := Over.homMk q
  exact ⟨Q', hQ, g, (Over.epi_iff_epi_left _).2 (by change Epi (q ≫ f.left); infer_instance)⟩

/-- An epimorphism from a member of `S` to the source of an object of the slice over `T` gives an
object of the slice with source in `S` and an epimorphism to it. -/
private lemma exists_S_over_epi_of_epi_left {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {S : Set (Sheaf J (Type u))} {T : Sheaf J (Type u)}
    (X : Over T) {Q : Sheaf J (Type u)} (hQ : Q ∈ S) (r : Q ⟶ X.left) (hr : Epi r) :
    ∃ Q' : Over T, Q'.left ∈ S ∧ ∃ f : Q' ⟶ X, Epi f :=
  ⟨Over.mk (r ≫ X.hom), hQ, Over.homMk r, (Over.epi_iff_epi_left _).2 hr⟩

/-- Property (3) of Stacks 0GN3 for the objects of the slice over `T` whose source lies in `S`,
given that fibre products of members of `S` over `T` are covered by members of `S`. -/
private lemma exists_S_over_cover_product {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    {T : Sheaf J (Type u)}
    (h_pullback : ∀ {A B : Sheaf J (Type u)}, A ∈ S → B ∈ S →
      ∀ (a : A ⟶ T) (b : B ⟶ T),
        ∃ Q ∈ S, ∃ q : Q ⟶ pullback a b, Sheaf.IsLocallySurjective q)
    (A B : Over T) (hA : A.left ∈ S) (hB : B.left ∈ S) :
    ∃ Q : Over T, Q.left ∈ S ∧ ∃ q : Q ⟶ A ⨯ B, Epi q := by
  obtain ⟨Q, hQ, q, hq⟩ := h_pullback hA hB A.hom B.hom
  have : Epi q := (Sheaf.isLocallySurjective_iff_epi q).1 hq
  exact exists_S_over_epi_of_epi_left (A ⨯ B) hQ (q ≫ (Over.prodLeftIsoPullback A B).inv)
    inferInstance

/-- Property (4) of Stacks 0GN3 for the objects of the slice over `T` whose source lies in `S`,
deduced from property (4) for `S`. -/
private lemma exists_S_over_cover_equalizer {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    (h_equalizer : ∀ {K K' : Sheaf J (Type u)} (a b : K ⟶ K'), K ∈ S → K' ∈ S →
      ∃ K'' ∈ S, ∃ f : K'' ⟶ equalizer a b, Sheaf.IsLocallySurjective f)
    {T : Sheaf J (Type u)} {A B : Over T} (a b : A ⟶ B)
    (hA : A.left ∈ S) (hB : B.left ∈ S) :
    ∃ Q : Over T, Q.left ∈ S ∧ ∃ q : Q ⟶ equalizer a b, Epi q := by
  obtain ⟨Q, hQ, q, hq⟩ := h_equalizer a.left b.left hA hB
  have : Epi q := (Sheaf.isLocallySurjective_iff_epi q).1 hq
  exact exists_S_over_epi_of_epi_left (equalizer a b) hQ
    (q ≫ (PreservesEqualizer.iso (Over.forget T) a b).inv) inferInstance


/-- Quasi-compactness of a sheaf of sets descends along a functor which preserves small
coproducts, preserves epimorphisms and reflects them. -/
public lemma isQuasiCompact_of_preserves_coproducts {C D : Type u}
    [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) L]
    [L.PreservesEpimorphisms] [L.ReflectsEpimorphisms]
    (X : Sheaf K (Type u)) (hX : Sheaf.IsQuasiCompact (L.obj X)) :
    Sheaf.IsQuasiCompact X := by
  have : HasColimitsOfSize.{u, u} (Sheaf J (Type u)) := Sheaf.instHasColimitsOfSize
  have : HasColimitsOfSize.{u, u} (Sheaf K (Type u)) := Sheaf.instHasColimitsOfSize
  intro I G f hf
  have : Epi (Sigma.desc f) := (Sheaf.isLocallySurjective_iff_epi _).1 hf
  have hL : Epi (Sigma.desc fun i => L.map (f i)) := by
    rw [← sigmaComparison_map_desc L G X f]
    infer_instance
  obtain ⟨T, hT, ht⟩ := hX I (fun i => L.obj (G i)) (fun i => L.map (f i))
    ((Sheaf.isLocallySurjective_iff_epi _).2 hL)
  refine ⟨T, hT, (Sheaf.isLocallySurjective_iff_epi _).2 ?_⟩
  apply L.epi_of_epi_map
  have hE : Epi (sigmaComparison L (fun i : T => G i.val) ≫
      L.map (Sigma.desc fun i : T => f i.val)) := by
    rw [sigmaComparison_map_desc]
    exact (Sheaf.isLocallySurjective_iff_epi _).1 ht
  exact epi_of_epi (sigmaComparison L (fun i : T => G i.val)) _

/-- If a topos of sheaves of sets is equivalent to the slice of another over `T`, then a sheaf
is quasi-compact as soon as the underlying sheaf of its image is. -/
@[sga "4 VI 1.5.1" "partial"]
public lemma isQuasiCompact_of_slice_equivalence {C D : Type u}
    [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (T : Sheaf J (Type u)) (E : Sheaf K (Type u) ≌ Over T)
    (X : Sheaf K (Type u)) (hX : Sheaf.IsQuasiCompact (E.functor.obj X).left) :
    Sheaf.IsQuasiCompact X := by
  have : (Over.forget T).PreservesEpimorphisms :=
    ⟨fun f => (Over.epi_iff_epi_left f).1 inferInstance⟩
  exact isQuasiCompact_of_preserves_coproducts J K (E.functor ⋙ Over.forget T) X hX

/-- The four covering properties (1)–(4) of Stacks 0GN3, written with epimorphisms in an
arbitrary finitely complete category, transport along an equivalence: the image of a set with
the properties has them. -/
public lemma covering_properties_equivalence
    {A B : Type*} [Category* A] [Category* B] [HasFiniteLimits A] [HasFiniteLimits B]
    (E : A ≌ B) (S : Set A)
    (ht : ∃ X ∈ S, Epi (terminal.from X))
    (hl : ∀ {X Y : A} (f : X ⟶ Y), Y ∈ S → Epi f →
      ∃ Z ∈ S, ∃ g : Z ⟶ X, Epi (g ≫ f))
    (hp : ∀ X ∈ S, ∀ Y ∈ S, ∃ Z ∈ S, ∃ f : Z ⟶ X ⨯ Y, Epi f)
    (he : ∀ {X Y : A} (f g : X ⟶ Y), X ∈ S → Y ∈ S →
      ∃ Z ∈ S, ∃ h : Z ⟶ equalizer f g, Epi h) :
    (∃ X ∈ E.functor.obj '' S, Epi (terminal.from X)) ∧
    (∀ {X Y : B} (f : X ⟶ Y), Y ∈ E.functor.obj '' S → Epi f →
      ∃ Z ∈ E.functor.obj '' S, ∃ g : Z ⟶ X, Epi (g ≫ f)) ∧
    (∀ X ∈ E.functor.obj '' S, ∀ Y ∈ E.functor.obj '' S,
      ∃ Z ∈ E.functor.obj '' S, ∃ f : Z ⟶ X ⨯ Y, Epi f) ∧
    (∀ {X Y : B} (f g : X ⟶ Y), X ∈ E.functor.obj '' S →
      Y ∈ E.functor.obj '' S →
      ∃ Z ∈ E.functor.obj '' S, ∃ h : Z ⟶ equalizer f g, Epi h) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨X, hX, h⟩ := ht
    let e := terminalIsoIsTerminal (terminalIsTerminal.isTerminalObj E.functor _)
    have hf : E.functor.map (terminal.from X) ≫ e.inv =
        terminal.from (E.functor.obj X) := terminal.hom_ext _ _
    exact ⟨E.functor.obj X, ⟨X, hX, rfl⟩, by rw [← hf]; infer_instance⟩
  · rintro X _ f ⟨Y, hY, rfl⟩ hf
    let f' : E.functor.obj (E.inverse.obj X) ⟶ E.functor.obj Y :=
      (E.counitIso.app X).hom ≫ f
    let a := E.functor.preimage f'
    have ha : Epi a := by
      apply E.functor.epi_of_epi_map
      dsimp [a]
      rw [Functor.map_preimage]
      dsimp [f']
      infer_instance
    obtain ⟨Z, hZ, g, hg⟩ := hl a hY ha
    refine ⟨E.functor.obj Z, ⟨Z, hZ, rfl⟩,
      E.functor.map g ≫ (E.counitIso.app X).hom, ?_⟩
    have hmap : Epi (E.functor.map (g ≫ a)) := inferInstance
    simpa only [Functor.map_comp, a, Functor.map_preimage, f', Category.assoc] using hmap
  · rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
    obtain ⟨Z, hZ, f, hf⟩ := hp X hX Y hY
    exact ⟨E.functor.obj Z, ⟨Z, hZ, rfl⟩,
      E.functor.map f ≫ prodComparison E.functor X Y, by infer_instance⟩
  · rintro _ _ f g ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
    let f' := E.functor.preimage f
    let g' := E.functor.preimage g
    obtain ⟨Z, hZ, h, hh⟩ := he f' g' hX hY
    let e : E.functor.obj (equalizer f' g') ≅ equalizer f g :=
      PreservesEqualizer.iso E.functor f' g' ≪≫
        eqToIso (by simp only [f', g', Functor.map_preimage])
    exact ⟨E.functor.obj Z, ⟨Z, hZ, rfl⟩, E.functor.map h ≫ e.hom, by infer_instance⟩

/-- **The localization step of Stacks 0GN3.** Let `S` satisfy hypotheses (1)–(5) of Stacks 0GN3
on a site `C`, let `K ∈ S` and let `n : ℕ`. Then the localized site `C/Kⁿ` carries a set `S'`
of sheaves of sets satisfying the same five hypotheses. -/
public lemma exists_localized_coveringSet {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_equalizer : ∀ {K K' : Sheaf J (Type u)} (a b : K ⟶ K'), K ∈ S → K' ∈ S →
      ∃ K'' ∈ S, ∃ f : K'' ⟶ equalizer a b, Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K)
    {K : Sheaf J (Type u)} (hK : K ∈ S) (n : ℕ) :
    let J' := (CostructuredArrow.proj yoneda (sheafPower J K n).obj).restrictedTopology J
    ∃ S' : Set (Sheaf J' (Type u)),
      (∃ X ∈ S', Sheaf.IsLocallySurjective (terminal.from X)) ∧
      (∀ {X Y : Sheaf J' (Type u)} (f : X ⟶ Y), Y ∈ S' →
        Sheaf.IsLocallySurjective f →
          ∃ Z ∈ S', ∃ g : Z ⟶ X, Sheaf.IsLocallySurjective (g ≫ f)) ∧
      (∀ X ∈ S', ∀ Y ∈ S', ∃ Z ∈ S', ∃ f : Z ⟶ X ⨯ Y,
        Sheaf.IsLocallySurjective f) ∧
      (∀ {X Y : Sheaf J' (Type u)} (f g : X ⟶ Y), X ∈ S' → Y ∈ S' →
        ∃ Z ∈ S', ∃ h : Z ⟶ equalizer f g, Sheaf.IsLocallySurjective h) ∧
      (∀ X ∈ S', Sheaf.IsQuasiCompact X) := by
  let T := sheafPower J K n
  let J' := (CostructuredArrow.proj yoneda T.obj).restrictedTopology J
  obtain ⟨_, _, E, _, _⟩ :=
    T.property.exists_sheafEquivalence_costructuredArrow_yoneda.2.2
  let S₀ : Set (Over T) := {Q | Q.left ∈ S}
  have ht : ∃ Q ∈ S₀, Epi (terminal.from Q) :=
    exists_S_over_cover_terminal J S
      (exists_S_cover_of_sheafPower J S h_terminal h_product hK n)
  have hl : ∀ {G Q : Over T} (f : G ⟶ Q), Q ∈ S₀ → Epi f →
      ∃ R ∈ S₀, ∃ g : R ⟶ G, Epi (g ≫ f) :=
    fun f hQ hf => exists_S_over_lift J S h_lift f hQ hf
  have hp : ∀ Q ∈ S₀, ∀ R ∈ S₀, ∃ P ∈ S₀, ∃ f : P ⟶ Q ⨯ R, Epi f :=
    fun Q hQ R hR => exists_S_over_cover_product J S
      (fun hA hB a b => exists_S_cover_pullback_sheafPower J S h_product h_equalizer
        hK n hA hB a b) Q R hQ hR
  have he : ∀ {Q R : Over T} (f g : Q ⟶ R), Q ∈ S₀ → R ∈ S₀ →
      ∃ P ∈ S₀, ∃ h : P ⟶ equalizer f g, Epi h :=
    fun f g hQ hR => exists_S_over_cover_equalizer J S h_equalizer f g hQ hR
  obtain ⟨ht', hl', hp', he'⟩ := covering_properties_equivalence E.symm S₀ ht hl hp he
  refine ⟨E.inverse.obj '' S₀, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨X, hX, hf⟩ := ht'
    exact ⟨X, hX, (Sheaf.isLocallySurjective_iff_epi _).2 hf⟩
  · intro X Y f hY hf
    obtain ⟨Z, hZ, g, hg⟩ := hl' f hY ((Sheaf.isLocallySurjective_iff_epi _).1 hf)
    exact ⟨Z, hZ, g, (Sheaf.isLocallySurjective_iff_epi _).2 hg⟩
  · intro X hX Y hY
    obtain ⟨Z, hZ, f, hf⟩ := hp' X hX Y hY
    exact ⟨Z, hZ, f, (Sheaf.isLocallySurjective_iff_epi _).2 hf⟩
  · intro X Y f g hX hY
    obtain ⟨Z, hZ, h, hh⟩ := he' f g hX hY
    exact ⟨Z, hZ, h, (Sheaf.isLocallySurjective_iff_epi _).2 hh⟩
  · rintro _ ⟨Q, hQ, rfl⟩
    apply isQuasiCompact_of_slice_equivalence J J' T E
    exact Sheaf.isQuasiCompact_of_isLocallySurjective (E.counitIso.app Q).inv.left
      ((Sheaf.isLocallySurjective_iff_epi _).2
        ((Over.epi_iff_epi_left _).1 inferInstance)) (h_quasiCompact Q.left hQ)


end Stacks.Cohomology.CoveringSet

end
