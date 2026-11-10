module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentReduction

/-!
# Gluing a functor on schemes over a base from open subfunctors

Let `G` be a presheaf of types on the schemes over a scheme `S` which is a sheaf for the Zariski
topology. Suppose `G` has a family of subfunctors `F i`, each representable, each cut out at
every scheme-valued point `ξ` of `G` over `T` by an open `W i T ξ` of `T`, and such that these
opens cover `T`. Then `G` is representable ([Stacks, Tag 01JJ], for the schemes over `S`).

This is the gluing criterion in the form used by the source's proofs of Tags 0B99 and 0B9A,
where the subfunctors are the families with a prescribed basis and the families supported in an
affine open respectively.

## Main results

* `Stacks.OverGluing.isRepresentable_of_openSubfunctors`: the gluing criterion.
* `Stacks.OverGluing.representable_of_totalRepresentable` and
  `Stacks.OverGluing.totalRepresentableBy`: representability transfers between a presheaf on
  the slice over `S` and its total presheaf on all schemes.

## Implementation notes

The proof passes to the total presheaf `Stacks.Sites.totalPresheaf G` on all schemes and applies
Mathlib's `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`. The elementary
calculus in the total presheaf is the one of
`StacksFrontier/AlgebraicGeometry/Morphisms/FiniteLocallyFree/Representability.lean`, where it is
private; it is restated publicly here.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites (totalPresheaf)

universe u v w

namespace Stacks.OverGluing

/-! ### Elementary calculus in the total presheaf -/

/-- Two elements of the total presheaf built from restrictions of one section along two
morphisms of the slice with the same underlying morphism of schemes agree. -/
lemma totalSigmaMkEq {C : Type w} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {V W : C} {φ : W ⟶ S} (s : F.obj (op (Over.mk φ)))
    {ψ ψ' : V ⟶ S} (e : Over.mk ψ ⟶ Over.mk φ) (e' : Over.mk ψ' ⟶ Over.mk φ)
    (h : e.left = e'.left) :
    (⟨ψ, F.map e.op s⟩ : Σ χ : V ⟶ S, F.obj (op (Over.mk χ))) = ⟨ψ', F.map e'.op s⟩ := by
  have h1 := Over.w e
  have h2 := Over.w e'
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  obtain rfl : ψ = ψ' := by rw [← h1, ← h2, h]
  rw [Over.OverMorphism.ext h]

/-- The section of `F` at `A` carried by an element of the total presheaf whose first component
is the structure morphism of `A`. -/
def totalSection {C : Type w} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A : Over S} (p : (totalPresheaf F).obj (op A.left))
    (h : p.1 = A.hom) : F.obj (op A) :=
  F.map (Over.homMk (𝟙 A.left) (by simpa using h) : A ⟶ Over.mk p.1).op p.2

/-- The first component of a restriction of an element of the total presheaf whose first
component is a structure morphism is again a structure morphism. -/
lemma totalMapFst {C : Type w} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A B : Over S} (b : B ⟶ A) {p : (totalPresheaf F).obj (op A.left)}
    (h : p.1 = A.hom) {q : (totalPresheaf F).obj (op B.left)}
    (hq : (totalPresheaf F).map b.left.op p = q) : q.1 = B.hom := by
  have hfst : b.left ≫ p.1 = q.1 := congrArg Sigma.fst hq
  rw [← hfst, h]
  exact Over.w b

/-- `Stacks.OverGluing.totalSection` recovers the element of the total presheaf it came from. -/
lemma totalMkSection {C : Type w} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A : Over S} (p : (totalPresheaf F).obj (op A.left)) (h : p.1 = A.hom) :
    (⟨A.hom, totalSection p h⟩ : (totalPresheaf F).obj (op A.left)) = p := by
  have h1 := totalSigmaMkEq p.2
    (Over.homMk (𝟙 A.left) (by simpa using h) : Over.mk A.hom ⟶ Over.mk p.1)
    (𝟙 (Over.mk p.1)) (by simp)
  have h2 : (⟨p.1, F.map (𝟙 (Over.mk p.1)).op p.2⟩ :
      (totalPresheaf F).obj (op A.left)) = p := by
    cases p
    simp
  exact h1.trans h2

/-- Restriction in the total presheaf of an element assembled from a section of `F`. -/
lemma totalMapMk {C : Type w} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A B : Over S} (b : B ⟶ A) (t : F.obj (op A)) :
    (totalPresheaf F).map b.left.op (⟨A.hom, t⟩ : (totalPresheaf F).obj (op A.left)) =
      ⟨B.hom, F.map b.op t⟩ := by
  change (⟨b.left ≫ A.hom,
    F.map (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom).op t⟩ :
      (totalPresheaf F).obj (op B.left)) = ⟨B.hom, F.map b.op t⟩
  exact totalSigmaMkEq t
    (Over.homMk b.left rfl : Over.mk (b.left ≫ A.hom) ⟶ Over.mk A.hom) b rfl

/-- Two elements of the total presheaf with the same first component agree as soon as their
second components do. -/
lemma totalSigmaSndInj {C : Type w} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {V : C} {φ : V ⟶ S} {s t : F.obj (op (Over.mk φ))}
    (hst : (⟨φ, s⟩ : Σ ψ : V ⟶ S, F.obj (op (Over.mk ψ))) = ⟨φ, t⟩) : s = t := by
  simpa using hst

/-- `Stacks.OverGluing.totalSection` commutes with restriction. -/
lemma totalMapSection {C : Type w} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {A B : Over S} (b : B ⟶ A) {p : (totalPresheaf F).obj (op A.left)}
    (h : p.1 = A.hom) {q : (totalPresheaf F).obj (op B.left)}
    (hq : (totalPresheaf F).map b.left.op p = q) :
    F.map b.op (totalSection p h) = totalSection q (totalMapFst b h hq) :=
  totalSigmaSndInj <| (totalMapMk b (totalSection p h)).symm.trans <|
    ((congrArg (fun s => (totalPresheaf F).map b.left.op s) (totalMkSection p h)).trans hq).trans
      (totalMkSection q (totalMapFst b h hq)).symm

/-- **Representability of the total presheaf implies representability of the presheaf on the
slice.**  The representing object of the slice presheaf is the representing scheme of the total
presheaf, equipped with the first component of the universal element as its structure
morphism. -/
lemma representable_of_totalRepresentable {C : Type w} [Category.{v} C] {S : C}
    {F : (Over S)ᵒᵖ ⥤ Type v} {W : C}
    (R : (totalPresheaf F).RepresentableBy W) : F.IsRepresentable := by
  let x := R.homEquiv (𝟙 W)
  let φ : W ⟶ S := x.1
  let A : Over S := Over.mk φ
  let t : F.obj (op A) := totalSection x rfl
  have hmap {B : Over S} (k : B ⟶ A) :
      (totalPresheaf F).map k.left.op x =
        (⟨B.hom, F.map k.op t⟩ : (totalPresheaf F).obj (op B.left)) := by
    rw [← totalMkSection (A := A) x rfl]
    exact totalMapMk k t
  let rep : F.RepresentableBy A := by
    refine
      { homEquiv := fun {B} =>
          Equiv.ofBijective (fun k : B ⟶ A => F.map k.op t) ?_
        homEquiv_comp := ?_ }
    · refine ⟨fun k₁ k₂ h ↦ ?_, fun y ↦ ?_⟩
      · apply Over.OverMorphism.ext
        apply R.homEquiv.injective
        have htotal : (totalPresheaf F).map k₁.left.op x =
            (totalPresheaf F).map k₂.left.op x := by
          calc
            _ = ⟨B.hom, F.map k₁.op t⟩ := hmap k₁
            _ = ⟨B.hom, F.map k₂.op t⟩ :=
              congrArg (fun z : F.obj (op B) =>
                (⟨B.hom, z⟩ : (totalPresheaf F).obj (op B.left))) h
            _ = _ := (hmap k₂).symm
        calc
          R.homEquiv k₁.left = (totalPresheaf F).map k₁.left.op x := R.homEquiv_eq _
          _ = (totalPresheaf F).map k₂.left.op x := htotal
          _ = R.homEquiv k₂.left := (R.homEquiv_eq _).symm
      · let p : (totalPresheaf F).obj (op B.left) := ⟨B.hom, y⟩
        let k₀ : B.left ⟶ W := R.homEquiv.symm p
        have hk : (totalPresheaf F).map k₀.op x = p := by
          simpa [k₀, x] using (R.homEquiv_eq k₀).symm.trans (R.homEquiv.apply_symm_apply p)
        let k : B ⟶ A := Over.homMk k₀ (congrArg Sigma.fst hk)
        exact ⟨k, totalSigmaSndInj ((hmap k).symm.trans hk)⟩
    · intro B B' b k
      exact F.map_comp_apply k.op b.op t
  exact rep.isRepresentable

/-- **Representability on the slice implies representability of the total presheaf.** The
representing scheme is the underlying scheme of the representing object of the slice. -/
def totalRepresentableBy {C : Type w} [Category.{v} C] {S : C} {F : (Over S)ᵒᵖ ⥤ Type v}
    {W : Over S} (R : F.RepresentableBy W) :
    (totalPresheaf F).RepresentableBy W.left := by
  let x : (totalPresheaf F).obj (op W.left) := ⟨W.hom, R.homEquiv (𝟙 W)⟩
  have hmap {A : Over S} (k : A ⟶ W) :
      (totalPresheaf F).map k.left.op x = ⟨A.hom, R.homEquiv k⟩ :=
    (totalMapMk k (R.homEquiv (𝟙 W))).trans
      (congrArg (fun z ↦ (⟨A.hom, z⟩ : (totalPresheaf F).obj (op A.left)))
        (R.homEquiv_eq k).symm)
  refine
    { homEquiv := fun {T} ↦ Equiv.ofBijective (fun k ↦ (totalPresheaf F).map k.op x) ?_
      homEquiv_comp := ?_ }
  · constructor
    · intro k l hkl
      have he : k ≫ W.hom = l ≫ W.hom := congrArg Sigma.fst hkl
      let A : Over S := Over.mk (k ≫ W.hom)
      let k' : A ⟶ W := Over.homMk k rfl
      let l' : A ⟶ W := Over.homMk l he.symm
      exact congrArg Over.Hom.left (R.homEquiv.injective
        (totalSigmaSndInj ((hmap k').symm.trans (hkl.trans (hmap l')))))
    · rintro ⟨a, m⟩
      exact ⟨(R.homEquiv.symm m).left,
        (hmap (R.homEquiv.symm m)).trans
          (congrArg (fun z ↦ (⟨a, z⟩ : (totalPresheaf F).obj (op T)))
            (R.homEquiv.apply_symm_apply m))⟩
  · intro T T' a b
    exact (totalPresheaf F).map_comp_apply b.op a.op x

/-! ### Charts from representable subfunctors -/

variable {S : Scheme.{u}}

/-- The morphism of total presheaves induced by a morphism of presheaves on the slice. -/
def totalMapOver {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G) :
    totalPresheaf F ⟶ totalPresheaf G where
  app T := ↾ fun x ↦ ⟨x.1, η.app _ x.2⟩
  naturality {T T'} k := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, m⟩
    exact congrArg (fun n ↦ (⟨k.unop ≫ a, n⟩ : (totalPresheaf G).obj T'))
      (η.naturality_apply _ m)

/-- The chart of the total presheaf of `G` attached to a representable subfunctor. -/
def subfunctorChart {G : (Over S)ᵒᵖ ⥤ Type u} (F : Subfunctor G) {W : Over S}
    (R : F.toFunctor.RepresentableBy W) : yoneda.obj W.left ⟶ totalPresheaf G :=
  (totalRepresentableBy R).toIso.hom ≫ totalMapOver F.ι

/-- The image of a chart attached to a subfunctor consists of the pairs whose second component
lies in the subfunctor. -/
theorem mem_range_subfunctorChart_iff {G : (Over S)ᵒᵖ ⥤ Type u} (F : Subfunctor G)
    {W : Over S} (R : F.toFunctor.RepresentableBy W) {T : Scheme.{u}}
    (x : (totalPresheaf G).obj (op T)) :
    x ∈ Set.range ((subfunctorChart F R).app (op T)) ↔ x.2 ∈ F.obj (op (Over.mk x.1)) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ((totalRepresentableBy R).homEquiv k).2.2
  · intro h
    refine ⟨(totalRepresentableBy R).homEquiv.symm ⟨x.1, ⟨x.2, h⟩⟩, ?_⟩
    change (totalMapOver F.ι).app _ ((totalRepresentableBy R).homEquiv
      ((totalRepresentableBy R).homEquiv.symm ⟨x.1, ⟨x.2, h⟩⟩)) = x
    have e := (totalRepresentableBy R).homEquiv.apply_symm_apply
      (show (totalPresheaf F.toFunctor).obj (op T) from ⟨x.1, ⟨x.2, h⟩⟩)
    rw [e]
    rfl

/-- Each component of a chart attached to a subfunctor is injective. -/
theorem subfunctorChart_injective {G : (Over S)ᵒᵖ ⥤ Type u} (F : Subfunctor G)
    {W : Over S} (R : F.toFunctor.RepresentableBy W) (T : Scheme.{u}ᵒᵖ) :
    Function.Injective ((subfunctorChart F R).app T) := by
  intro k l hkl
  apply (totalRepresentableBy R).homEquiv.injective
  change (totalMapOver F.ι).app _ ((totalRepresentableBy R).homEquiv k) =
    (totalMapOver F.ι).app _ ((totalRepresentableBy R).homEquiv l) at hkl
  generalize (totalRepresentableBy R).homEquiv k = p at hkl
  generalize (totalRepresentableBy R).homEquiv l = q at hkl
  obtain ⟨a, y⟩ := p
  obtain ⟨b, z⟩ := q
  change (⟨a, y.1⟩ : (totalPresheaf G).obj T) = ⟨b, z.1⟩ at hkl
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj hkl
  exact congrArg (Sigma.mk a) (Subtype.ext (eq_of_heq h2))

/-- **Stacks Project, Tag 01JJ, for the schemes over a base, with open subfunctors.** Let `G` be
a Zariski sheaf of types on the schemes over `S` and let `F i` be representable subfunctors of
`G`. Suppose that every scheme-valued point `ξ` of `G` over `T` comes with opens `W i T ξ` of
`T` such that a base change of `ξ` along `h : Y ⟶ T` lies in `F i` exactly when `h` lands in
`W i T ξ`, and that these opens cover `T`. Then `G` is representable. -/
theorem isRepresentable_of_openSubfunctors (G : (Over S)ᵒᵖ ⥤ Type u)
    (hG : Presieve.IsSheaf (Scheme.zariskiTopology.over S) G)
    {ι : Type u} (F : ι → Subfunctor G) (hrep : ∀ i, (F i).toFunctor.IsRepresentable)
    (W : ∀ (_i : ι) (T : Over S), G.obj (op T) → T.left.Opens)
    (hW : ∀ (i : ι) (T Y : Over S) (ξ : G.obj (op T)) (h : Y ⟶ T),
      G.map h.op ξ ∈ (F i).obj (op Y) ↔ ∀ y : Y.left, h.left y ∈ W i T ξ)
    (hcov : ∀ (T : Over S) (ξ : G.obj (op T)) (t : T.left), ∃ i, t ∈ W i T ξ) :
    G.IsRepresentable := by
  have openImmersion_presheaf_of_range : ∀ {F : Scheme.{u}ᵒᵖ ⥤ Type u}
      {W : Scheme.{u}} (η : yoneda.obj W ⟶ F)
      (hinj : ∀ T, Function.Injective (η.app T))
      (hopen : ∀ (T : Scheme.{u}) (x : F.obj (op T)),
        ∃ O : T.Opens, ∀ (T' : Scheme.{u}) (e : T' ⟶ T),
          (∃ k : T' ⟶ W, η.app _ k = F.map e.op x) ↔ ∀ t, e t ∈ O),
      IsOpenImmersion.presheaf η := by
    intro F W η hinj hopen
    apply MorphismProperty.relative.of_exists
    intro T ζ
    obtain ⟨O, hO⟩ := hopen T (yonedaEquiv ζ)
    obtain ⟨k, hk⟩ := (hO O.toScheme O.ι).2 (fun t ↦ t.property)
    have comm : yoneda.map k ≫ η = yoneda.map O.ι ≫ ζ := by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hk.trans (map_yonedaEquiv _ _)
    refine ⟨O.toScheme, yoneda.map k, O.ι, ?_, inferInstance⟩
    apply IsPullback.iff_app.mpr
    intro T'
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨congrArg (fun n ↦ n.app T') comm, fun a b hab ↦ (cancel_mono O.ι).1 hab.2, ?_⟩
    intro a e he
    change T'.unop ⟶ W at a
    change T'.unop ⟶ T at e
    have heO : ∀ t, e t ∈ O := (hO T'.unop e).1 ⟨a, he.trans (map_yonedaEquiv _ _).symm⟩
    let l : T'.unop ⟶ O.toScheme := IsOpenImmersion.lift O.ι e (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨e t, heO t⟩, rfl⟩)
    have hl : l ≫ O.ι = e := IsOpenImmersion.lift_fac _ _ _
    refine ⟨l, ?_, hl⟩
    apply hinj T'
    have hc := congrArg (fun n : yoneda.obj O.toScheme ⟶ F ↦ n.app T' l) comm
    change η.app T' (l ≫ k) = ζ.app T' (l ≫ O.ι) at hc
    exact hc.trans ((congrArg (ζ.app T') hl).trans he.symm)
  let : Scheme.zariskiTopology.{u}.Subcanonical := Scheme.subcanonical_zariskiTopology
  have hy : Presieve.IsSheaf Scheme.zariskiTopology.{u} (yoneda.obj S) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  let P := totalPresheaf G
  have hP : Presieve.IsSheaf Scheme.zariskiTopology P :=
    (Stacks.Sites.isSheaf_over_iff_isSheaf_totalPresheaf _ G hy).1 hG
  let Psh : Sheaf Scheme.zariskiTopology (Type u) := ⟨P, (isSheaf_iff_isSheaf_of_type _ _).2 hP⟩
  choose Wo hWo using fun i ↦ (hrep i).has_representation
  let R (i : ι) : (F i).toFunctor.RepresentableBy (Wo i) := (hWo i).some
  let c (i : ι) : yoneda.obj (Wo i).left ⟶ P := subfunctorChart (F i) (R i)
  have hopen (i : ι) : IsOpenImmersion.presheaf (c i) := by
    apply openImmersion_presheaf_of_range
    · exact subfunctorChart_injective (F i) (R i)
    · intro T x
      refine ⟨W i (Over.mk x.1) x.2, fun T' e ↦ ?_⟩
      refine Iff.trans ?_ (hW i (Over.mk x.1) (Over.mk (e ≫ x.1)) x.2 (Over.homMk e rfl))
      exact mem_range_subfunctorChart_iff (F i) (R i) (P.map e.op x)
  have hsurj : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c) := by
    constructor
    intro T x
    let O (i : ι) : T.Opens := W i (Over.mk x.1) x.2
    let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers ι
      (fun i ↦ (O i).toScheme) (fun i ↦ (O i).ι) (by
        intro t
        obtain ⟨i, hi⟩ := hcov (Over.mk x.1) x.2 t
        exact ⟨i, ⟨t, hi⟩, rfl⟩)
    apply Scheme.zariskiTopology.superset_covering ?_ 𝒰.mem_grothendieckTopology
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    obtain ⟨k, hk⟩ : P.map (O i).ι.op x ∈ Set.range ((c i).app (op (O i).toScheme)) :=
      (mem_range_subfunctorChart_iff (F i) (R i) _).2
        ((hW i (Over.mk x.1) (Over.mk ((O i).ι ≫ x.1)) x.2 (Over.homMk (O i).ι rfl)).2
          fun y ↦ y.2)
    exact ⟨(Sigma.ι (fun i ↦ yoneda.obj (Wo i).left) i).app _ k,
      (congrArg (fun n : yoneda.obj (Wo i).left ⟶ P ↦ n.app (op (O i).toScheme) k)
        (Sigma.ι_comp_desc c i)).trans hk⟩
  have : P.IsRepresentable :=
    Scheme.LocalRepresentability.isRepresentable (F := Psh) (f := c) hopen
  exact representable_of_totalRepresentable P.representableBy

/-! ### Bijectivity from affine probes -/

/-- A family of morphisms over `S` whose underlying morphisms are jointly surjective open
immersions generates a covering sieve of the Zariski topology over `S`. -/
theorem ofArrows_mem_zariskiTopology_over {Y : Over S} {ι : Type u} (Z : ι → Over S)
    (α : ∀ i, Z i ⟶ Y) (hα : ∀ i, IsOpenImmersion (α i).left)
    (hcov : ∀ y : Y.left, ∃ i z, (α i).left z = y) :
    Sieve.ofArrows Z α ∈ (Scheme.zariskiTopology.over S) Y := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Scheme.Cover.mkOfCovers ι (fun i ↦ (Z i).left) (fun i ↦ (α i).left) hcov
    (fun i ↦ hα i)).mem_grothendieckTopology

/-- Two sections of a separated presheaf over `Y` agree if their restrictions along a family of
open immersions jointly covering `Y` agree. -/
private theorem eq_of_map_ofArrows_eq {P : (Over S)ᵒᵖ ⥤ Type u}
    (hP : Presieve.IsSeparated (Scheme.zariskiTopology.over S) P) {Y : Over S} {ι : Type u}
    (Z : ι → Over S) (α : ∀ i, Z i ⟶ Y) (hα : ∀ i, IsOpenImmersion (α i).left)
    (hcov : ∀ y : Y.left, ∃ i z, (α i).left z = y) {x x' : P.obj (op Y)}
    (h : ∀ i, P.map (α i).op x = P.map (α i).op x') : x = x' := by
  refine (Presieve.isSeparatedFor_iff_generate.mpr
    (hP _ (ofArrows_mem_zariskiTopology_over Z α hα hcov))).ext fun W f hf ↦ ?_
  obtain ⟨i⟩ := hf
  exact h i

/-- **A morphism from a Zariski sheaf to a separated presheaf on the schemes over `S` is
bijective** as soon as it is injective at the affine schemes `Spec A ⟶ S` and every section of
the target lies, near every point, in its image along an open immersion. -/
theorem bijective_app_of_probes {F G : (Over S)ᵒᵖ ⥤ Type u} (η : F ⟶ G)
    (hF : Presieve.IsSheaf (Scheme.zariskiTopology.over S) F)
    (hG : Presieve.IsSeparated (Scheme.zariskiTopology.over S) G)
    (hinj : ∀ (A : CommRingCat.{u}) (s : Spec A ⟶ S),
      Function.Injective (η.app (op (Over.mk s))))
    (hloc : ∀ (Y : Over S) (ξ : G.obj (op Y)) (y : Y.left), ∃ (Z : Over S) (α : Z ⟶ Y),
      IsOpenImmersion α.left ∧ y ∈ Set.range α.left ∧ G.map α.op ξ ∈ Set.range (η.app (op Z)))
    (Y : Over S) : Function.Bijective (η.app (op Y)) := by
  -- injectivity everywhere, from injectivity on affine probes
  have hinjAll : ∀ Y : Over S, Function.Injective (η.app (op Y)) := by
    intro Y x x' hxx
    have hV : ∀ y : Y.left, ∃ V : Y.left.Opens, IsAffineOpen V ∧ y ∈ V := fun y ↦ by
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
        Y.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      exact ⟨V, hV, hyV⟩
    choose V hVa hyV using hV
    let Z (y : Y.left) : Over S := Over.mk ((hVa y).fromSpec ≫ Y.hom)
    let α (y : Y.left) : Z y ⟶ Y := Over.homMk (hVa y).fromSpec rfl
    refine eq_of_map_ofArrows_eq hF.isSeparated Z α (fun y ↦ inferInstanceAs
      (IsOpenImmersion (hVa y).fromSpec)) (fun y ↦ ?_) fun y ↦ ?_
    · obtain ⟨z, hz⟩ : y ∈ Set.range (hVa y).fromSpec := by
        rw [(hVa y).range_fromSpec]
        exact hyV y
      exact ⟨y, z, hz⟩
    · apply hinj
      rw [η.naturality_apply, η.naturality_apply, hxx]
  refine ⟨hinjAll Y, fun ξ ↦ ?_⟩
  choose Z α hαo hαy hαr using hloc Y ξ
  choose k hk using hαr
  have hsieve := ofArrows_mem_zariskiTopology_over Z α hαo (fun y ↦ ⟨y, hαy y⟩)
  have hsh := (Presieve.isSheafFor_iff_generate (Presieve.ofArrows Z α)).mpr (hF _ hsieve)
  have hcompat : Presieve.Arrows.Compatible F α k := by
    intro i j W a b hab
    apply hinjAll
    rw [η.naturality_apply, η.naturality_apply, hk, hk, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hab]
  obtain ⟨x, hx, -⟩ := (Presieve.isSheafFor_arrows_iff (π := α) (P := F)).mp hsh k hcompat
  refine ⟨x, ?_⟩
  refine eq_of_map_ofArrows_eq hG Z α hαo (fun y ↦ ⟨y, hαy y⟩) fun y ↦ ?_
  rw [← η.naturality_apply, hx, hk]

end Stacks.OverGluing

end
