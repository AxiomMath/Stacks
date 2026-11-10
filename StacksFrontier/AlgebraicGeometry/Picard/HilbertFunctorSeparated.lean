module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafInclusion
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.WeilRestriction
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOfPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hilbert scheme of points is separated

Let `X` be a scheme over a base `S` and let `d` be a natural number.  If the degree-`d` Hilbert
functor of `X` is representable by a scheme `H` over `S`, then `H ⟶ S` is separated.

## Main results

* `Stacks.Hilbert.isSeparated_of_representsHilbertFunctorOfRank` is Tag 0B98.
* `Stacks.Hilbert.isSeparated_of_representsHilbertFunctorOfRank'` is the same conclusion for an
  arbitrary `X ⟶ S`, the separatedness the source assumes being unused.

## Implementation notes

The diagonal of `H ⟶ S` is shown to be a closed immersion directly, which is what separatedness
means.  Write `Q = H ×_S H`, let `p₁, p₂ : Q ⟶ H` be the two projections and let
`I, J ⊆ 𝒪_{X ×_S Q}` be the ideal sheaves of the two families `Z₁ = p₁^* Z` and `Z₂ = p₂^* Z`
obtained by pulling back the universal family `Z` along them.  Because `H` represents the
functor, a morphism `T ⟶ Q` factors through the diagonal exactly when the two families agree
after pulling back to `T`, that is exactly when the two ideal sheaves agree there.

The source forms the intersection `Z₁ ∩ Z₂` as the fibre product `Z₁ ×_{X_Q} Z₂`.  Here the two
families are presented by ideal sheaves on one and the same scheme `X ×_S Q`, so their
intersection is the closed subscheme cut out by `I ⊔ J`, and the two inclusions
`(I ⊔ J).subscheme ⟶ I.subscheme` and `(J ⊔ I).subscheme ⟶ J.subscheme` are closed immersions
with no further argument.  Each inclusion is base changed along the structure morphism of the
corresponding family, which is finite locally free of rank `d`, hence of finite presentation and
flat by Tag 02KB and pure relative to the base because it is proper; so Tag 07AI represents the
locus where it becomes an isomorphism by a closed immersion `W₁ ⟶ Q`, resp. `W₂ ⟶ Q`.

The scheme `R = W₁ ×_Q W₂` is therefore a closed subscheme of `Q` on which both inclusions
become isomorphisms, i.e. on which `I` and `J` have the same inverse image, i.e. through which
the two projections to `H` agree.  That makes `R ⟶ Q` factor through the diagonal; conversely
the diagonal satisfies the two isomorphism conditions, because `I` and `J` pull back to the same
ideal sheaf along it, so the diagonal factors through `R ⟶ Q`.  The two factorisations are
mutually inverse, so `R ⟶ H` is an isomorphism and the diagonal is a closed immersion.

`isIso_overPullback_exactSubschemeMap_iff_comap_eq` is the translation between the two
descriptions of each isomorphism condition: Tag 07AI phrases it as a base-changed morphism of
schemes over `Q` being an isomorphism, while the computation above is about inverse images of
ideal sheaves on `X ×_S Q`.  The source states the lemma for a separated `X ⟶ S`; the argument
above establishes it for an arbitrary `X ⟶ S`, because forming the intersection of the two
families as `I ⊔ J` needs no separatedness.  So the argument is carried out once, in the primed
statement, and the statement of the source is the specialisation of it.

## References

* [Stacks Project, Tag 0B98](https://stacks.math.columbia.edu/tag/0B98)
* [Stacks Project, Tag 0B97](https://stacks.math.columbia.edu/tag/0B97)
* [Stacks Project, Tag 07AI](https://stacks.math.columbia.edu/tag/07AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

/-! ### Isomorphism conditions and inverse images of ideal sheaves -/

/-- The kernel of the base change `T ×_Y I.subscheme ⟶ T` of the inclusion of a closed subscheme
along `f : T ⟶ Y` is the inverse image of `I` along `f`. -/
private theorem ker_pullback_snd_subschemeι {Y T : Scheme.{u}} (f : T ⟶ Y)
    (I : Y.IdealSheafData) : (pullback.snd I.subschemeι f).ker = I.comap f := by
  rw [← pullbackSymmetry_hom_comp_fst]
  exact Scheme.Hom.ker_comp_of_isIso _ _

/-- Base changing a morphism `I.subscheme ⟶ J.subscheme` of closed subschemes of `Y` over `Y`
along `f : T ⟶ Y` gives an isomorphism exactly when the inverse images of `I` and `J` along `f`
agree: both morphisms into `T` are closed immersions with those inverse images as kernels. -/
private theorem isIso_pullbackMap_subschemeι_iff_comap_eq {Y T : Scheme.{u}}
    (f : T ⟶ Y) (I J : Y.IdealSheafData) (i : I.subscheme ⟶ J.subscheme)
    (hi : i ≫ J.subschemeι = I.subschemeι) :
    IsIso (pullback.map I.subschemeι f J.subschemeι f i (𝟙 T) (𝟙 Y)
      hi.symm (by simp)) ↔ I.comap f = J.comap f := by
  let ψ := pullback.map I.subschemeι f J.subschemeι f i (𝟙 T) (𝟙 Y) hi.symm (by simp)
  have hcomp : ψ ≫ pullback.snd J.subschemeι f = pullback.snd I.subschemeι f := by
    dsimp [ψ, pullback.map]
    exact pullback.lift_snd _ _ _
  have hI := ker_pullback_snd_subschemeι f I
  have hJ := ker_pullback_snd_subschemeι f J
  refine ⟨fun _ => ?_, fun hker =>
    IsClosedImmersion.isIso_of_ker_eq _ _ ψ hcomp (hI.trans (hker.trans hJ.symm))⟩
  rw [← hI, ← hJ, ← hcomp]
  exact Scheme.Hom.ker_comp_of_isIso _ _

/-- A morphism `I.subscheme ⟶ J.subscheme` of closed subschemes of `Q`, read as a morphism of
schemes over a base `B` via `q : Q ⟶ B`. -/
private def subschemeMapOver {B Q : Scheme.{u}} (q : Q ⟶ B)
    {I J : Q.IdealSheafData} (i : I.subscheme ⟶ J.subscheme)
    (hi : i ≫ J.subschemeι = I.subschemeι) :
    Over.mk (I.subschemeι ≫ q) ⟶ Over.mk (J.subschemeι ≫ q) :=
  Over.homMk i (congrArg (fun g => g ≫ q) hi)

/-- Base changing `subschemeMapOver` along `e : T ⟶ B` gives an isomorphism exactly when the
inverse images of `I` and `J` along the projection `Q ×_B T ⟶ Q` agree.  The two base changes
differ by the pasting isomorphism `(Q ×_B T) ×_Q I.subscheme ≅ I.subscheme ×_B T`. -/
private theorem isIso_overPullback_subschemeMap_iff_comap_eq {B Q T : Scheme.{u}}
    (q : Q ⟶ B) (e : T ⟶ B) (I J : Q.IdealSheafData)
    (i : I.subscheme ⟶ J.subscheme) (hi : i ≫ J.subschemeι = I.subschemeι) :
    IsIso (((Over.pullback e).map (subschemeMapOver q i hi)).left) ↔
      I.comap (pullback.fst q e) = J.comap (pullback.fst q e) := by
  let u := subschemeMapOver q i hi
  let η := ((Over.pullback e).map u).left
  let r := pullback.fst q e
  let α : pullback (I.subschemeι ≫ q) e ≅ pullback I.subschemeι r :=
    (pullbackRightPullbackFstIso q e _).symm
  let β : pullback (J.subschemeι ≫ q) e ≅ pullback J.subschemeι r :=
    (pullbackRightPullbackFstIso q e _).symm
  let φ := pullback.map I.subschemeι r J.subschemeι r i (𝟙 _) (𝟙 Q) hi.symm (by simp)
  have hηfst : η ≫ pullback.fst (J.subschemeι ≫ q) e =
      pullback.fst (I.subschemeι ≫ q) e ≫ i := by
    dsimp [η, Over.pullback, u, subschemeMapOver]
    simp
    rfl
  have hηsnd : η ≫ pullback.snd (J.subschemeι ≫ q) e =
      pullback.snd (I.subschemeι ≫ q) e := by
    dsimp [η, Over.pullback, u, subschemeMapOver]
    simp
  have hφfst : φ ≫ pullback.fst J.subschemeι r =
      pullback.fst I.subschemeι r ≫ i := by
    dsimp [φ, pullback.map]
    simp
  have hφsnd : φ ≫ pullback.snd J.subschemeι r =
      pullback.snd I.subschemeι r := by
    dsimp [φ, pullback.map]
    simp
  have htransport : α.hom ≫ φ = η ≫ β.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφfst]
      simp [α, β, r, hηfst]
    · apply pullback.hom_ext
      · simp [α, β, r, reassoc_of% hφsnd, reassoc_of% hηfst, hi]
      · simp [α, β, r, reassoc_of% hφsnd, hηsnd]
  have hIso : IsIso η ↔ IsIso φ := by
    calc
      IsIso η ↔ IsIso (η ≫ β.hom) :=
        (MorphismProperty.cancel_right_of_respectsIso (@IsIso Scheme _) η β.hom).symm
      _ ↔ IsIso (α.hom ≫ φ) := by rw [htransport]
      _ ↔ IsIso φ := MorphismProperty.cancel_left_of_respectsIso (@IsIso Scheme _) α.hom φ
  exact hIso.trans (isIso_pullbackMap_subschemeι_iff_comap_eq r I J i hi)

/-- The form of `isIso_overPullback_subschemeMap_iff_comap_eq` in which Tag 07AI phrases its
isomorphism condition: the source of the morphism of schemes over `B` is presented as
`Over.mk (i ≫ (I.subschemeι ≫ q))` rather than as `Over.mk (K.subschemeι ≫ q)`. -/
private theorem isIso_overPullback_exactSubschemeMap_iff_comap_eq
    {B P T : Scheme.{u}} (q : P ⟶ B) (e : T ⟶ B)
    (K I : P.IdealSheafData) (i : K.subscheme ⟶ I.subscheme)
    (hi : i ≫ I.subschemeι = K.subschemeι) :
    IsIso (((Over.pullback e).map
      (Over.homMk i (by simp) :
        Over.mk (i ≫ (I.subschemeι ≫ q)) ⟶ Over.mk (I.subschemeι ≫ q))).left) ↔
      K.comap (pullback.fst q e) = I.comap (pullback.fst q e) := by
  let a : Over.mk (i ≫ (I.subschemeι ≫ q)) ⟶ Over.mk (I.subschemeι ≫ q) :=
    Over.homMk i (by simp)
  let c := subschemeMapOver q i hi
  have hbase : i ≫ (I.subschemeι ≫ q) = K.subschemeι ≫ q := by rw [← hi, Category.assoc]
  let e₀ : Over.mk (i ≫ (I.subschemeι ≫ q)) ≅ Over.mk (K.subschemeι ≫ q) :=
    Over.isoMk (Iso.refl _) hbase.symm
  have hmap : ((Over.pullback e).map a).left =
      ((Over.pullback e).map e₀.hom).left ≫ ((Over.pullback e).map c).left := by
    rw [show a = e₀.hom ≫ c from Over.OverMorphism.ext rfl, Functor.map_comp, Over.comp_left]
  have : IsIso ((Over.pullback e).map e₀.hom).left :=
    (Over.forget T).map_isIso ((Over.pullback e).map e₀.hom)
  rw [hmap]
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsIso Scheme _) _ _).trans
    (isIso_overPullback_subschemeMap_iff_comap_eq q e K I i hi)

/-- The inverse images of `I` and `J` agree exactly when those of `I ⊔ J` and `I` agree and those
of `J ⊔ I` and `J` agree. -/
private theorem comap_eq_comap_iff_comap_sup {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I J : Y.IdealSheafData) :
    I.comap f = J.comap f ↔ (I ⊔ J).comap f = I.comap f ∧ (J ⊔ I).comap f = J.comap f := by
  simp only [Scheme.IdealSheafData.comap_sup, sup_eq_left]
  exact le_antisymm_iff.trans and_comm

/-! ### The Weil restriction of a closed subscheme of a finite locally free family -/

/-- Tag 07AI applies to the inclusion `(A ⊔ A').subscheme ⟶ A.subscheme` of closed subschemes of
`P`, when `A.subscheme ⟶ P ⟶ B` is finite locally free of rank `d`: such a morphism is of finite
presentation and flat by Tag 02KB, and pure relative to `B` because it is proper.  So a closed
subscheme `W ⟶ B` exists which a scheme `t : T ⟶ B` over `B` maps to exactly when the inverse
images of `A ⊔ A'` and `A` along the projection `P ×_B T ⟶ P` agree. -/
@[sga "3 XI 6.1" "special case"]
private theorem exists_closedImmersion_hom_iff_comap_sup_eq {B P : Scheme.{u}} (q : P ⟶ B)
    (A A' : P.IdealSheafData) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (A.subschemeι ≫ q) d] :
    ∃ W : Over B, IsClosedImmersion W.hom ∧ ∀ {T : Scheme.{u}} (t : T ⟶ B),
      Nonempty (Over.mk t ⟶ W) ↔
        (A ⊔ A').comap (pullback.fst q t) = A.comap (pullback.fst q t) := by
  obtain ⟨_, _, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (A.subschemeι ≫ q)).mp (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d)
  obtain ⟨W, hW, ⟨e⟩⟩ :=
    Stacks.Flatness.weilRestriction_representableBy_closedImmersion_of_affineTests
      (Scheme.IdealSheafData.inclusion (le_sup_left : A ≤ A ⊔ A')) (A.subschemeι ≫ q)
      fun s D _ _ => AlgebraicGeometry.isSchemeUniversallyPureRelative_of_isProper _ s D
  refine ⟨W, hW, fun t => ?_⟩
  exact (Iff.intro (fun ⟨g⟩ => (e.homEquiv g).down) fun h => ⟨e.homEquiv.symm ⟨h⟩⟩).trans
    (isIso_overPullback_exactSubschemeMap_iff_comap_eq q t _ _ _
      (Scheme.IdealSheafData.inclusion_subschemeι _))

/-- Inverse images along the projection `(X ×_S Q) ×_Q T ⟶ X ×_S Q` and along the base change
map `X ×_S T ⟶ X ×_S Q` of a morphism `u : T ⟶ Q` agree, because the base change map factors
through the projection. -/
private theorem comap_familyBaseChangeMap_eq_of_comap_pullback_eq {S : Scheme.{u}}
    (X Q T : Over S) (u : T ⟶ Q) (I J : (pullback X.hom Q.hom).IdealSheafData)
    (h : I.comap (pullback.fst ((Over.pullback Q.hom).obj X).hom u.left) =
      J.comap (pullback.fst ((Over.pullback Q.hom).obj X).hom u.left)) :
    I.comap (familyBaseChangeMap X u) = J.comap (familyBaseChangeMap X u) := by
  let b := familyBaseChangeMap X u
  let π := ((Over.pullback Q.hom).obj X).hom
  have hb : b ≫ π = pullback.snd X.hom T.hom ≫ u.left := by
    dsimp [b, π, familyBaseChangeMap]
    simp [pullback.map]
  let t : ((Over.pullback T.hom).obj X).left ⟶ pullback π u.left :=
    pullback.lift b (pullback.snd X.hom T.hom) hb
  have ht : t ≫ pullback.fst π u.left = b :=
    pullback.lift_fst _ _ _
  change I.comap b = J.comap b
  rw [← ht, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
  exact congrArg (·.comap t) h

/-- Two morphisms `f₁ f₂ : T ⟶ H` into a representing scheme of the Hilbert functor agree after
composing with `t : Z ⟶ T` exactly when the ideal sheaves of the two families they classify have
the same inverse image on `(X ×_S T) ×_T Z`. -/
private theorem comp_left_eq_iff_comap_eq {S : Scheme.{u}} {X H : Over S} {d : ℕ}
    (hH : RepresentsHilbertFunctorOfRank X H d) {T : Over S} (f₁ f₂ : T ⟶ H)
    {Z : Scheme.{u}} (t : Z ⟶ T.left) :
    t ≫ f₁.left = t ≫ f₂.left ↔
      (hH.family f₁).ideal.comap (pullback.fst (pullback.snd X.hom T.hom) t) =
        (hH.family f₂).ideal.comap (pullback.fst (pullback.snd X.hom T.hom) t) := by
  refine ⟨fun ht => ?_, fun h => ?_⟩
  · have hc : pullback.fst (pullback.snd X.hom T.hom) t ≫ familyBaseChangeMap X f₁ =
        pullback.fst (pullback.snd X.hom T.hom) t ≫ familyBaseChangeMap X f₂ := by
      dsimp only [familyBaseChangeMap, pullback.map]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd,
          pullback.condition_assoc, pullback.condition_assoc, ht]
    rw [← Category.comp_id f₁, ← Category.comp_id f₂, hH.naturality f₁, hH.naturality f₂,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hc]
  · let u : Over.mk (t ≫ T.hom) ⟶ T := Over.homMk t rfl
    have hu : (hH.family (u ≫ f₁)).ideal = (hH.family (u ≫ f₂)).ideal := by
      rw [hH.naturality u f₁, hH.naturality u f₂]
      exact comap_familyBaseChangeMap_eq_of_comap_pullback_eq X T _ u _ _ h
    simpa [u] using congrArg Over.Hom.left (hH.family.injective (HilbertFamily.ext hu))

/-- A morphism `δ` is a closed immersion when it factors as `d ≫ r` through a closed immersion
`r`, where `d` is a section of a morphism `g` with `g ≫ δ = r`. -/
private theorem isClosedImmersion_of_comp_eq {R H Q : Scheme.{u}} {r : R ⟶ Q} {δ : H ⟶ Q}
    [IsClosedImmersion r] (g : R ⟶ H) (d : H ⟶ R) (hg : g ≫ δ = r) (hd : d ≫ r = δ)
    (hdg : d ≫ g = 𝟙 H) : IsClosedImmersion δ := by
  have : IsIso g :=
    ⟨⟨d, (cancel_mono r).1 (by rw [Category.assoc, hd, hg, Category.id_comp]), hdg⟩⟩
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion g δ).mp
    (by rwa [hg])

/-! ### Tag 0B98 -/

/-- **The Hilbert scheme of points is separated, for an arbitrary `X ⟶ S`.** Let `X` be a scheme
over `S` and let `d` be a natural number.  If the degree-`d` Hilbert functor of `X` is represented
by a scheme `H` over `S`, then `H ⟶ S` is separated.

This is Tag 0B98 with the hypothesis that `X ⟶ S` be separated dropped: the argument forms the
intersection of the two pulled-back families as `I ⊔ J`, which needs no separatedness.  The
statement of the source is `Stacks.Hilbert.isSeparated_of_representsHilbertFunctorOfRank`, which
is this one applied to a separated `X ⟶ S`. -/
public theorem isSeparated_of_representsHilbertFunctorOfRank' {S : Scheme.{u}}
    (X H : Over S) (d : ℕ)
    (hH : RepresentsHilbertFunctorOfRank X H d) :
    IsSeparated H.hom := by
  let Q := pullback H.hom H.hom
  let p₁ : Q ⟶ H.left := pullback.fst H.hom H.hom
  let p₂ : Q ⟶ H.left := pullback.snd H.hom H.hom
  let q : Q ⟶ S := p₁ ≫ H.hom
  let T : Over S := Over.mk q
  let f₁ : T ⟶ H := Over.homMk p₁ rfl
  let f₂ : T ⟶ H := Over.homMk p₂ pullback.condition.symm
  let I := (hH.family f₁).ideal
  let J := (hH.family f₂).ideal
  let π : ((Over.pullback q).obj X).left ⟶ Q := pullback.snd X.hom q
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ π) d :=
    (hH.family f₁).isFiniteLocallyFreeOfRank
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (J.subschemeι ≫ π) d :=
    (hH.family f₂).isFiniteLocallyFreeOfRank
  obtain ⟨W₁, hW₁closed, hW₁⟩ := exists_closedImmersion_hom_iff_comap_sup_eq π I J d
  obtain ⟨W₂, hW₂closed, hW₂⟩ := exists_closedImmersion_hom_iff_comap_sup_eq π J I d
  let r : pullback W₁.hom W₂.hom ⟶ Q := pullback.fst W₁.hom W₂.hom ≫ W₁.hom
  have hK_I := (hW₁ r).mp ⟨Over.homMk (pullback.fst W₁.hom W₂.hom) rfl⟩
  have hK_J := (hW₂ r).mp ⟨Over.homMk (pullback.snd W₁.hom W₂.hom) pullback.condition.symm⟩
  have hg : r ≫ p₁ = r ≫ p₂ := (comp_left_eq_iff_comap_eq hH f₁ f₂ r).mpr
    ((comap_eq_comap_iff_comap_sup _ I J).mpr ⟨hK_I, hK_J⟩)
  let δ : H.left ⟶ Q := pullback.diagonal H.hom
  have hδ₁ : δ ≫ p₁ = 𝟙 H.left := by simp [δ, p₁]
  have hδ₂ : δ ≫ p₂ = 𝟙 H.left := by simp [δ, p₂]
  obtain ⟨hKδI, hKδJ⟩ := (comap_eq_comap_iff_comap_sup _ I J).mp
    ((comp_left_eq_iff_comap_eq hH f₁ f₂ δ).mp (hδ₁.trans hδ₂.symm))
  obtain ⟨d₁⟩ := (hW₁ δ).mpr hKδI
  obtain ⟨d₂⟩ := (hW₂ δ).mpr hKδJ
  let d : H.left ⟶ pullback W₁.hom W₂.hom :=
    pullback.lift d₁.left d₂.left (d₁.w.trans d₂.w.symm)
  have hd : d ≫ r = δ := by simp [d, r]
  have hrFactor : (r ≫ p₁) ≫ δ = r := by
    apply pullback.hom_ext
    · rw [Category.assoc, hδ₁, Category.comp_id]
    · rwa [Category.assoc, hδ₂, Category.comp_id]
  exact ⟨isClosedImmersion_of_comp_eq (r ≫ p₁) d hrFactor hd (by rw [reassoc_of% hd, hδ₁])⟩

/-- **Stacks Project, Tag 0B98.** Let `X ⟶ S` be separated and let `d` be a natural number.  If
the degree-`d` Hilbert functor of `X` is represented by a scheme `H` over `S`, then `H ⟶ S` is
separated.

The separatedness of `X ⟶ S` which the source assumes is not used:
`Stacks.Hilbert.isSeparated_of_representsHilbertFunctorOfRank'` is the same conclusion for an
arbitrary `X ⟶ S`, and this is that statement specialised to the hypotheses of the source. -/
@[stacks 0B98]
public theorem isSeparated_of_representsHilbertFunctorOfRank {S : Scheme.{u}}
    (X H : Over S) (d : ℕ) [IsSeparated X.hom]
    (hH : RepresentsHilbertFunctorOfRank X H d) :
    IsSeparated H.hom :=
  isSeparated_of_representsHilbertFunctorOfRank' X H d hH

end Stacks.Hilbert
