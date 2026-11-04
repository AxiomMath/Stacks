module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf

/-!
# The Hilbert functor of points read on all schemes

Let `X` be a scheme over `S` and `d` a natural number. The degree-`d` Hilbert functor of `X` is
a functor on the schemes over `S`. Read on all schemes, it is the presheaf

  `T ↦ {(s, Z) : s : T ⟶ S, Z a degree-d Hilbert family in X over (T, s)}`,

which is the form to which the representability criterion of Stacks Tag 01JJ, as formalised in
Mathlib (`AlgebraicGeometry.Scheme.LocalRepresentability`), applies. This file sets it up and
shows that a scheme representing it, viewed over `S` through the structure morphism classifying
the universal pair, represents the Hilbert functor in the sense of
`Stacks.Hilbert.RepresentsHilbertFunctorOfRank`.

## Main definitions

* `Stacks.Hilbert.familyPullback`: base change of a Hilbert family along a morphism of schemes
  compatible with the structure morphisms.
* `Stacks.Hilbert.hilbPresheaf`: the Hilbert functor read on all schemes.
* `Stacks.Hilbert.representsOfRepresentableBy`: a representing scheme of `hilbPresheaf` represents
  the Hilbert functor of points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}} (X : Over S) (d : ℕ)

/-- The comparison map of fibre products depends only on the underlying morphism of schemes. -/
theorem familyBaseChangeMap_homMk_congr {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S}
    {a b : T' ⟶ T} (e : a = b) (ha : a ≫ s = s') (hb : b ≫ s = s') :
    familyBaseChangeMap X (Over.homMk a ha : Over.mk s' ⟶ Over.mk s) =
      familyBaseChangeMap X (Over.homMk b hb : Over.mk s' ⟶ Over.mk s) := by
  subst e
  rfl

/-- The comparison maps of fibre products along `a : T'' ⟶ T'` and `b : T' ⟶ T` compose to the
comparison map along `a ≫ b`. -/
theorem familyBaseChangeMap_comp_homMk {T T' T'' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S}
    {s'' : T'' ⟶ S} (a : T'' ⟶ T') (b : T' ⟶ T) (ha : a ≫ s' = s'') (hb : b ≫ s = s')
    (hab : (a ≫ b) ≫ s = s'') :
    familyBaseChangeMap X (Over.homMk a ha : Over.mk s'' ⟶ Over.mk s') ≫
        familyBaseChangeMap X (Over.homMk b hb : Over.mk s' ⟶ Over.mk s) =
      familyBaseChangeMap X (Over.homMk (a ≫ b) hab : Over.mk s'' ⟶ Over.mk s) := by
  rw [← familyBaseChangeMap_comp]
  rfl

/-- Base change of a Hilbert family along a morphism of schemes compatible with the structure
morphisms to `S`. -/
def familyPullback {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (g : T' ⟶ T)
    (h : g ≫ s = s') (Z : HilbertFamily X (Over.mk s) d) : HilbertFamily X (Over.mk s') d :=
  baseChange X (Over.homMk g h : Over.mk s' ⟶ Over.mk s) Z

/-- The ideal sheaf of the base change of `Z` along `g` is the pullback of the ideal sheaf of `Z`
along the comparison map of fibre products. -/
theorem familyPullback_ideal {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (g : T' ⟶ T)
    (h : g ≫ s = s') (Z : HilbertFamily X (Over.mk s) d) :
    (familyPullback X d g h Z).ideal =
      Z.ideal.comap (familyBaseChangeMap X (Over.homMk g h : Over.mk s' ⟶ Over.mk s)) :=
  rfl

/-- The sections of the Hilbert presheaf over a scheme `T`. -/
abbrev HilbSections (T : Scheme.{u}) : Type u := Σ s : T ⟶ S, HilbertFamily X (Over.mk s) d

/-- The comparison map of fibre products along the identity of `T` is the identity. -/
theorem familyBaseChangeMap_homMk_id {T : Scheme.{u}} {s : T ⟶ S} (h : 𝟙 T ≫ s = s) :
    familyBaseChangeMap X (Over.homMk (𝟙 T) h : Over.mk s ⟶ Over.mk s) = 𝟙 _ :=
  familyBaseChangeMap_id X (Over.mk s)

/-- Pulling back an ideal sheaf along the comparison map for the identity of `T` leaves it
unchanged. -/
theorem comap_familyBaseChangeMap_homMk_id {T : Scheme.{u}} {s : T ⟶ S} (h : 𝟙 T ≫ s = s)
    (I : ((Over.pullback (Over.mk s).hom).obj X).left.IdealSheafData) :
    I.comap (familyBaseChangeMap X (Over.homMk (𝟙 T) h : Over.mk s ⟶ Over.mk s)) = I := by
  rw [familyBaseChangeMap_homMk_id]
  exact Scheme.IdealSheafData.comap_id I

/-- **Equality of sections of the Hilbert presheaf.** Two pairs are equal exactly when the
structure morphisms agree and the ideal sheaves correspond under the canonical identification
of the two fibre products. -/
theorem sigma_eq_iff {T : Scheme.{u}} {s s' : T ⟶ S} (Z : HilbertFamily X (Over.mk s) d)
    (Z' : HilbertFamily X (Over.mk s') d) :
    (⟨s, Z⟩ : HilbSections X d T) = ⟨s', Z'⟩ ↔
      ∃ e : s = s', Z'.ideal = Z.ideal.comap (familyBaseChangeMap X
        (Over.homMk (𝟙 T) (by change 𝟙 T ≫ s = s'; rw [Category.id_comp, e]) :
          Over.mk s' ⟶ Over.mk s)) := by
  constructor
  · intro h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    obtain rfl := eq_of_heq h
    exact ⟨rfl, (comap_familyBaseChangeMap_homMk_id X _ _).symm⟩
  · rintro ⟨rfl, h⟩
    congr 1
    refine HilbertFamily.ext ?_
    rw [h]
    exact (comap_familyBaseChangeMap_homMk_id X _ _).symm

/-- **The Hilbert functor of points read on all schemes.** Its sections over `T` are pairs of a
morphism `s : T ⟶ S` and a degree-`d` Hilbert family in `X` over `(T, s)`. -/
def hilbPresheaf : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := HilbSections X d T.unop
  map g := ↾fun p ↦ ⟨g.unop ≫ p.1, familyPullback X d g.unop rfl p.2⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, Z⟩
    change (⟨𝟙 T.unop ≫ s, familyPullback X d (𝟙 T.unop) rfl Z⟩ : HilbSections X d T.unop) =
      ⟨s, Z⟩
    rw [sigma_eq_iff]
    refine ⟨Category.id_comp s, ?_⟩
    rw [familyPullback_ideal, ← Scheme.IdealSheafData.comap_comp,
      familyBaseChangeMap_comp_homMk (hab := by simp),
      familyBaseChangeMap_homMk_congr X (Category.id_comp (𝟙 T.unop)) _ (Category.id_comp s)]
    exact (comap_familyBaseChangeMap_homMk_id X _ _).symm
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨s, Z⟩
    change (⟨(g.unop ≫ f.unop) ≫ s, familyPullback X d (g.unop ≫ f.unop) rfl Z⟩ :
      HilbSections X d _) =
        ⟨g.unop ≫ f.unop ≫ s, familyPullback X d g.unop rfl (familyPullback X d f.unop rfl Z)⟩
    rw [sigma_eq_iff]
    refine ⟨Category.assoc _ _ _, ?_⟩
    rw [familyPullback_ideal, familyPullback_ideal, familyPullback_ideal,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    congr 1
    rw [familyBaseChangeMap_comp_homMk (hab := by simp),
      familyBaseChangeMap_comp_homMk (hab := by simp)]
    exact familyBaseChangeMap_homMk_congr X (by simp) _ _

/-- The structure morphism of the pullback of a section `p` along `g` is `g ≫ p.1`. -/
@[simp]
theorem hilbPresheaf_map_fst {T T' : Scheme.{u}} (g : T' ⟶ T) (p : (hilbPresheaf X d).obj (op T)) :
    ((hilbPresheaf X d).map g.op p).1 = g ≫ p.1 :=
  rfl

/-- The ideal sheaf of the pullback of a section `p` along `g` is the pullback of the ideal sheaf
of `p` along the comparison map of fibre products. -/
theorem hilbPresheaf_map_snd_ideal {T T' : Scheme.{u}} (g : T' ⟶ T)
    (p : (hilbPresheaf X d).obj (op T)) :
    ((hilbPresheaf X d).map g.op p).2.ideal =
      p.2.ideal.comap
        (familyBaseChangeMap X (Over.homMk g rfl : Over.mk (g ≫ p.1) ⟶ Over.mk p.1)) :=
  rfl

/-- Two sections of the Hilbert presheaf with the same structure morphism and the same ideal sheaf
are equal. -/
theorem sigma_eq_of_ideal_eq {T : Scheme.{u}} {s : T ⟶ S} (Z Z' : HilbertFamily X (Over.mk s) d)
    (h : Z.ideal = Z'.ideal) :
    (⟨s, Z⟩ : (hilbPresheaf X d).obj (op T)) = ⟨s, Z'⟩ := by
  rw [HilbertFamily.ext h]

/-! ### From a representing scheme of the presheaf to the Hilbert functor -/

section Represents

variable {X d} {H : Scheme.{u}} (rep : (hilbPresheaf X d).RepresentableBy H)

/-- The structure morphism to `S` of a scheme representing the Hilbert presheaf. -/
def repStructure : H ⟶ S := (rep.homEquiv (𝟙 H)).1

/-- The universal family over a scheme representing the Hilbert presheaf. -/
def repFamily :
    HilbertFamily X (Over.mk (repStructure rep)) d :=
  (rep.homEquiv (𝟙 H)).2

/-- The section of the Hilbert presheaf corresponding to `f : T ⟶ H` is the pullback of the
universal pair along `f`. -/
theorem repHomEquiv_eq {T : Scheme.{u}} (f : T ⟶ H) :
    rep.homEquiv f = ⟨f ≫ repStructure rep,
      familyPullback X d f rfl (repFamily rep)⟩ := by
  have := rep.homEquiv_comp f (𝟙 H)
  rw [Category.comp_id] at this
  rw [this]
  rfl

/-- The structure morphism of the section corresponding to `f : T ⟶ H` is
`f ≫ repStructure rep`. -/
theorem repHomEquiv_fst {T : Scheme.{u}} (f : T ⟶ H) :
    (rep.homEquiv f).1 = f ≫ repStructure rep := by
  rw [repHomEquiv_eq rep]

/-- The sections of the Hilbert presheaf over `T.left` lying over the structure morphism of `T`
are the Hilbert families over `T`. -/
def fiberEquiv (X : Over S) (d : ℕ) (T : Over S) :
    {p : (hilbPresheaf X d).obj (op T.left) // p.1 = T.hom} ≃ HilbertFamily X T d where
  toFun p := familyPullback X d (𝟙 T.left) (by rw [Category.id_comp]; exact p.2) p.1.2
  invFun Z := ⟨⟨T.hom, Z⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨s, Z⟩, h⟩
    obtain rfl : s = T.hom := h
    exact Subtype.ext (sigma_eq_of_ideal_eq X d _ _ (comap_familyBaseChangeMap_homMk_id X _ _))
  right_inv Z := HilbertFamily.ext (comap_familyBaseChangeMap_homMk_id X _ _)

/-- If a section `p` lying over `T.hom` is the pair `(s, Z)`, then the ideal sheaf of the Hilbert
family `fiberEquiv X d T p` is the pullback of the ideal sheaf of `Z` along the comparison map
for the identity of `T.left`. -/
theorem fiberEquiv_ideal_of_eq (T : Over S) (p : {p : (hilbPresheaf X d).obj (op T.left) //
    p.1 = T.hom}) {s : T.left ⟶ S} (Z : HilbertFamily X (Over.mk s) d)
    (hp : p.1 = (⟨s, Z⟩ : HilbSections X d T.left)) (hs : s = T.hom) :
    (fiberEquiv X d T p).ideal = Z.ideal.comap (familyBaseChangeMap X
      (Over.homMk (𝟙 T.left) (by rw [Category.id_comp]; exact hs) : T ⟶ Over.mk s)) := by
  obtain ⟨p, hp'⟩ := p
  subst hp
  rfl

/-- Morphisms into `Over.mk σ` are morphisms of schemes compatible with the structure maps. -/
def overHomEquiv {H : Scheme.{u}} (T : Over S) (σ : H ⟶ S) :
    (T ⟶ Over.mk σ) ≃ {h : T.left ⟶ H // h ≫ σ = T.hom} where
  toFun φ := ⟨φ.left, Over.w φ⟩
  invFun h := Over.homMk h.1 h.2
  left_inv φ := by ext; rfl
  right_inv _ := rfl

/-- **A scheme representing the Hilbert presheaf represents the Hilbert functor of points**,
viewed over `S` through the structure morphism of the universal pair. -/
def representsOfRepresentableBy :
    RepresentsHilbertFunctorOfRank X (Over.mk (repStructure rep)) d where
  family {T} :=
    ((overHomEquiv T (repStructure rep)).trans
      (rep.homEquiv.subtypeEquiv (q := fun p => p.1 = T.hom) fun h => by
        rw [repHomEquiv_fst rep])).trans
        (fiberEquiv X d T)
  naturality {T' T} g f := by
    simp only [Equiv.trans_apply]
    rw [fiberEquiv_ideal_of_eq T' _ _ (repHomEquiv_eq rep (g ≫ f).left) (Over.w (g ≫ f)),
      fiberEquiv_ideal_of_eq T _ _ (repHomEquiv_eq rep f.left) (Over.w f),
      familyPullback_ideal, familyPullback_ideal, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    congr 1
    rw [familyBaseChangeMap_comp_homMk (hab := by simpa using Over.w (g ≫ f)),
      ← familyBaseChangeMap_comp, ← familyBaseChangeMap_comp]
    congr 1

end Represents

end Stacks.Hilbert

end
