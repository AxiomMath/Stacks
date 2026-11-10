module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget

/-!
# Representing the Hilbert functor of points by a universal family, locally on the base

Let `X` be a scheme over `S`. A scheme `H` over `S` together with a degree-`d` Hilbert family
`U` in `X` over `H` represents the degree-`d` Hilbert functor as soon as pulling `U` back along
morphisms `T ⟶ H` is a bijection onto the degree-`d` families over `T`, for every `S`-scheme
`T`. This file proves that this bijectivity may be checked locally on `T`: it suffices that two
morphisms classifying the same family agree near every point, and that every family is,
near every point, the pullback of `U`. It also records that being a Hilbert family is local on
the base.

## Main definitions

* `Stacks.Hilbert.Over.restrict` — the open subscheme of an `S`-scheme, as an `S`-scheme.
* `Stacks.Hilbert.RepresentsHilbertFunctorOfRank.ofUniversal` — the representability datum of a
  universal family whose pullback maps are bijective.

## Main results

* `Stacks.Hilbert.bijective_baseChange_of_local` — bijectivity of the pullback maps of a family
  follows from local uniqueness and local existence of classifying morphisms.
* `Stacks.Hilbert.isFiniteLocallyFreeOfRank_of_restrict` — an ideal sheaf on `X ×_S T` whose
  restrictions over an open cover of `T` are Hilbert families is a Hilbert family.

## Implementation notes

The gluing of the local classifying morphisms is `AlgebraicGeometry.Scheme.Cover.glueMorphisms`
for the open cover of `T` by the given neighbourhoods; that the glued morphism classifies the
given family is the separatedness of the Hilbert functor for flat covers,
`Stacks.Hilbert.hilbertFamily_ext_of_baseChange_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-- An open subscheme of an `S`-scheme, as an `S`-scheme. -/
abbrev Over.restrict (T : Over S) (V : T.left.Opens) : Over S := Over.mk (V.ι ≫ T.hom)

/-- The inclusion of an open subscheme, as a morphism of `S`-schemes. -/
abbrev Over.restrictι (T : Over S) (V : T.left.Opens) : Over.restrict T V ⟶ T :=
  Over.homMk V.ι rfl

variable (X : Over S) {H : Over S} {d : ℕ}

/-- **A universal family with bijective pullback maps represents the Hilbert functor.** -/
def RepresentsHilbertFunctorOfRank.ofUniversal (U : HilbertFamily X H d)
    (h : ∀ T : Over S, Function.Bijective fun g : T ⟶ H ↦ baseChange X g U) :
    RepresentsHilbertFunctorOfRank X H d where
  family {T} := Equiv.ofBijective _ (h T)
  naturality g f := by
    change (baseChange X (g ≫ f) U).ideal = (baseChange X f U).ideal.comap _
    rw [baseChange_comp, baseChange_ideal]

/-- Two morphisms of `S`-schemes into `H` agreeing near every point of the source are equal. -/
theorem Over.hom_ext_of_forall {T : Over S} (g g' : T ⟶ H)
    (h : ∀ t : T.left, ∃ V : T.left.Opens, t ∈ V ∧
      Over.restrictι T V ≫ g = Over.restrictι T V ≫ g') : g = g' := by
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t ↦ ?_)
  obtain ⟨V, htV, hV⟩ := h t
  exact ⟨V, htV, congrArg CommaMorphism.left hV⟩

/-- The open cover of a scheme given by a family of open immersions that jointly cover it. -/
private abbrev openCoverOfCovering {Y : Scheme.{u}} {ι : Type*} {Z : ι → Scheme.{u}}
    (f : ∀ i, Z i ⟶ Y) (hcov : ∀ y : Y, ∃ i, ∃ z : Z i, f i z = y)
    (hf : ∀ i, IsOpenImmersion (f i)) : Y.OpenCover where
  I₀ := ι
  X := Z
  f := f
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨hcov, hf⟩

/-- **Local criterion for a universal family.** Let `U` be a degree-`d` family over `H`. If two
morphisms classifying the same family agree near every point, and if every family is near every
point the pullback of `U` along some open immersion, then pulling `U` back is bijective over every
`S`-scheme. -/
theorem bijective_baseChange_of_local (U : HilbertFamily X H d)
    (hinj : ∀ (T : Over S) (g g' : T ⟶ H), baseChange X g U = baseChange X g' U →
      ∀ t : T.left, ∃ V : T.left.Opens, t ∈ V ∧
        Over.restrictι T V ≫ g = Over.restrictι T V ≫ g')
    (hsurj : ∀ (T : Over S) (D : HilbertFamily X T d) (t : T.left),
      ∃ (V : Over S) (i : V ⟶ T) (_ : IsOpenImmersion i.left) (v : V.left), i.left v = t ∧
        ∃ g : V ⟶ H, baseChange X g U = baseChange X i D)
    (T : Over S) : Function.Bijective fun g : T ⟶ H ↦ baseChange X g U := by
  have inj : ∀ T : Over S, Function.Injective fun g : T ⟶ H ↦ baseChange X g U :=
    fun T g g' hgg' ↦ Over.hom_ext_of_forall g g' (hinj T g g' hgg')
  refine ⟨inj T, fun D ↦ ?_⟩
  choose V i hi v hv g hg using hsurj T D
  let 𝒰 := openCoverOfCovering (fun t ↦ (i t).left) (fun t ↦ ⟨t, v t, hv t⟩) hi
  have hcompat : ∀ x y : T.left, pullback.fst (i x).left (i y).left ≫ (g x).left =
      pullback.snd (i x).left (i y).left ≫ (g y).left := by
    intro x y
    let P : Over S := Over.mk (pullback.fst (i x).left (i y).left ≫ (V x).hom)
    let a : P ⟶ V x := Over.homMk (pullback.fst _ _) rfl
    let b : P ⟶ V y := Over.homMk (pullback.snd _ _) (by
      change pullback.snd _ _ ≫ (V y).hom = pullback.fst _ _ ≫ (V x).hom
      rw [← Over.w (i x), ← Over.w (i y), pullback.condition_assoc])
    have hab : a ≫ i x = b ≫ i y := Over.OverMorphism.ext pullback.condition
    have : a ≫ g x = b ≫ g y := inj P <| by
      change baseChange X (a ≫ g x) U = baseChange X (b ≫ g y) U
      rw [baseChange_comp, baseChange_comp, hg x, hg y, ← baseChange_comp, ← baseChange_comp, hab]
    exact congrArg CommaMorphism.left this
  let gl : T.left ⟶ H.left := 𝒰.glueMorphisms (fun t ↦ (g t).left) hcompat
  have hgl (t : T.left) : (i t).left ≫ gl = (g t).left := 𝒰.ι_glueMorphisms _ hcompat t
  have hover : gl ≫ H.hom = T.hom := by
    refine 𝒰.hom_ext _ _ fun t ↦ ?_
    change (i t).left ≫ gl ≫ H.hom = (i t).left ≫ T.hom
    rw [← Category.assoc, hgl, Over.w (g t), Over.w (i t)]
  refine ⟨Over.homMk gl hover, hilbertFamily_ext_of_baseChange_eq X i
    (fun t ↦ inferInstanceAs (Flat (i t).left)) (fun t ↦ ⟨t, v t, hv t⟩) fun t ↦ ?_⟩
  rw [← baseChange_comp, ← hg t]
  congr 1
  exact Over.OverMorphism.ext (hgl t)

/-- The pullback of `I.subschemeι` along `g.left` is finite locally free of rank `d` once the
pulled-back family `I.comap (familyBaseChangeMap X g)` over `V` is. -/
private theorem property_pullback_snd_of_comap {T V : Over S}
    (I : ((Over.pullback T.hom).obj X).left.IdealSheafData) (d : ℕ) (g : V ⟶ T)
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((I.comap (familyBaseChangeMap X g)).subschemeι ≫ ((Over.pullback V.hom).obj X).hom) d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d
      (pullback.snd (I.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) g.left) := by
  rw [← (isPullback_familyBaseChangeMap_subschemeι X g I).isoPullback_inv_snd]
  refine (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr ?_
  rwa [Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff]

/-- **Being a Hilbert family is local on the base.** An ideal sheaf on `X ×_S T` whose
restrictions over the members of an open cover of `T` are finite locally free of rank `d` is
itself finite locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_of_restrict {T : Over S}
    (I : ((Over.pullback T.hom).obj X).left.IdealSheafData) (d : ℕ) (𝒰 : T.left.OpenCover)
    (h : ∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((I.comap (familyBaseChangeMap X
        (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T))).subschemeι ≫
          ((Over.pullback (𝒰.f i ≫ T.hom)).obj X).hom) d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (I.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) d := by
  rw [← Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff]
  exact IsZariskiLocalAtTarget.of_openCover 𝒰 fun i ↦
    property_pullback_snd_of_comap X I d
      (Over.homMk (𝒰.f i) rfl : Over.mk (𝒰.f i ≫ T.hom) ⟶ T) (h i)

/-- **Being a Hilbert family is local on the base**, for a cover by open immersions of
`S`-schemes. -/
theorem isFiniteLocallyFreeOfRank_of_cover {T : Over S}
    (I : ((Over.pullback T.hom).obj X).left.IdealSheafData) (d : ℕ) {ι : Type*}
    (V : ι → Over S) (g : ∀ i, V i ⟶ T) [hg : ∀ i, IsOpenImmersion (g i).left]
    (hcov : ∀ t : T.left, ∃ i, ∃ v : (V i).left, (g i).left v = t)
    (h : ∀ i, Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((I.comap (familyBaseChangeMap X (g i))).subschemeι ≫
        ((Over.pullback (V i).hom).obj X).hom) d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (I.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) d := by
  let 𝒰 := openCoverOfCovering (fun i ↦ (g i).left) hcov hg
  rw [← Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff]
  exact IsZariskiLocalAtTarget.of_openCover 𝒰 fun i ↦
    property_pullback_snd_of_comap X I d (g i) (h i)

end Stacks.Hilbert

end
