module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Transport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of finite étale covers to a dense open of a locally Noetherian scheme

Let `X` be a locally Noetherian scheme and `U ⊆ X` a dense open such that for every point `x` of
`X` outside `U` the punctured spectrum of every strict henselization of `𝒪_{X, x}` is connected.
Then base change of finite étale covers along `U ⟶ X` is fully faithful.

This is [Stacks, Tag 0BQF] with the hypothesis that the underlying space of `X` is Noetherian
weakened to `X` being locally Noetherian. The Noetherian case is
`AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_dense_of_noetherianSpace`; the general
case follows because fullness of restriction to a dense open is local on `X`.

## Main results

* `AlgebraicGeometry.full_finiteEtaleBaseChange_of_openCover`: let `U ⊆ X` be a dense open and
  `𝒱` an open cover of `X`. If restriction of finite étale covers from each member `V` of `𝒱` to
  the preimage of `U` in `V` is full, then restriction from `X` to `U` is full.
* `AlgebraicGeometry.nonempty_fullyFaithful_finiteEtaleBaseChange_of_openCover`: the same for full
  faithfulness.
* `AlgebraicGeometry.IsConnectedPuncturedStrictHenselization.of_ringEquiv`: the local hypothesis
  of [Stacks, Tag 0BQF] only depends on the local ring up to isomorphism.
* `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_dense_of_isLocallyNoetherian`:
  [Stacks, Tag 0BQF] for a locally Noetherian scheme.

## Implementation notes

Let `Y` and `Z` be finite étale over `X` and `φ` a morphism of their restrictions to `U`. On a
member `V` of the cover, fullness gives a morphism `Y_V ⟶ Z` over `X` restricting to `φ` over
`U ∩ V`. Two such morphisms agree on the overlap of their domains, because they agree on the
preimage of `U` there, which is dense since `Y ⟶ X` is open
(`AlgebraicGeometry.eq_of_isDominant_of_finiteEtale`). So they glue to a morphism `Y ⟶ Z` over
`X` (`AlgebraicGeometry.Scheme.Cover.glueMorphisms`), which restricts to `φ` over `U`.

## References

* [Stacks Project, Tag 0BQE](https://stacks.math.columbia.edu/tag/0BQE)
* [Stacks Project, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Extending a morphism of restricted covers over one member of a cover -/

/-- Let `T ⟶ V` be the base change of `i : U ⟶ X` along `ιV : V ⟶ X`, and suppose base change
of finite étale covers along `T ⟶ V` is full. Then a morphism `φ : Y ×_X U ⟶ Z ×_X U` over `U`,
for two finite étale covers `Y` and `Z` of `X`, induces a morphism `t : Y ×_X V ⟶ Z` over `X`
which agrees with `φ` on every part of `Y ×_X V` lying over `U`. -/
private lemma exists_hom_of_full_finiteEtaleBaseChange {X U V T : Scheme.{u}} {i : U ⟶ X}
    {ιV : V ⟶ X} {k : T ⟶ U} {j : T ⟶ V} (hsq : IsPullback k j i ιV)
    [(finiteEtaleBaseChange j).Full] (Y Z : FiniteEtaleOver X)
    (φ : pullback Y.hom i ⟶ pullback Z.hom i)
    (hφ : φ ≫ pullback.snd Z.hom i = pullback.snd Y.hom i) :
    ∃ t : pullback Y.hom ιV ⟶ Z.left, t ≫ Z.hom = pullback.snd Y.hom ιV ≫ ιV ∧
      ∀ {W : Scheme.{u}} (a : W ⟶ pullback Y.hom ιV) (b : W ⟶ U)
        (h : (a ≫ pullback.fst Y.hom ιV) ≫ Y.hom = b ≫ i),
        a ≫ t = pullback.lift (a ≫ pullback.fst Y.hom ιV) b h ≫ φ ≫ pullback.fst Z.hom i := by
  let a₀ : pullback (pullback.snd Y.hom ιV) j ⟶ pullback Y.hom ιV := pullback.fst _ _
  let s₀ : pullback (pullback.snd Y.hom ιV) j ⟶ T := pullback.snd _ _
  have hc₀ : (a₀ ≫ pullback.fst Y.hom ιV) ≫ Y.hom = (s₀ ≫ k) ≫ i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, hsq.w]
  let u : pullback (pullback.snd Y.hom ιV) j ⟶ Z.left :=
    pullback.lift _ _ hc₀ ≫ φ ≫ pullback.fst Z.hom i
  have hu : u ≫ Z.hom = (a₀ ≫ pullback.snd Y.hom ιV) ≫ ιV := by
    simp only [u, Category.assoc, pullback.condition, reassoc_of% hφ, pullback.lift_snd_assoc]
    rw [hsq.w, ← Category.assoc s₀, ← pullback.condition]
    simp only [a₀, Category.assoc]
  let v : pullback (pullback.snd Y.hom ιV) j ⟶ pullback Z.hom ιV := pullback.lift u _ hu
  let w : pullback (pullback.snd Y.hom ιV) j ⟶ pullback (pullback.snd Z.hom ιV) j :=
    pullback.lift v s₀ (by rw [pullback.lift_snd]; exact pullback.condition)
  -- fullness of base change along `j`, in terms of the underlying morphisms
  obtain ⟨g, hgw, hnat⟩ : ∃ g : pullback Y.hom ιV ⟶ pullback Z.hom ιV,
      g ≫ pullback.snd Z.hom ιV = pullback.snd Y.hom ιV ∧
        a₀ ≫ g = w ≫ pullback.fst (pullback.snd Z.hom ιV) j := by
    let ψ : (finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange ιV).obj Y) ⟶
        (finiteEtaleBaseChange j).obj ((finiteEtaleBaseChange ιV).obj Z) :=
      MorphismProperty.Over.homMk w (pullback.lift_snd _ _ _)
    obtain ⟨g, hg⟩ := (finiteEtaleBaseChange j).map_surjective ψ
    refine ⟨g.left, MorphismProperty.Over.w g, ?_⟩
    have hnat := finiteEtaleBaseChange_map_left_fst j g
    rw [hg] at hnat
    exact hnat.symm
  refine ⟨g ≫ pullback.fst Z.hom ιV, ?_, fun {W} a b h => ?_⟩
  · rw [Category.assoc, pullback.condition, reassoc_of% hgw]
  have hb : b ≫ i = (a ≫ pullback.snd Y.hom ιV) ≫ ιV := by
    rw [← h, Category.assoc, Category.assoc, pullback.condition]
  let p : W ⟶ pullback (pullback.snd Y.hom ιV) j :=
    pullback.lift a (hsq.lift b _ hb) (hsq.lift_snd _ _ _).symm
  have hpa : p ≫ a₀ = a := pullback.lift_fst _ _ _
  have hps : p ≫ s₀ ≫ k = b := by
    rw [← Category.assoc, pullback.lift_snd, hsq.lift_fst]
  have hlift : p ≫ pullback.lift (a₀ ≫ pullback.fst Y.hom ιV) (s₀ ≫ k) hc₀ =
      pullback.lift (a ≫ pullback.fst Y.hom ιV) b h := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, hpa]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hps]
  calc a ≫ g ≫ pullback.fst Z.hom ιV
      = p ≫ (a₀ ≫ g) ≫ pullback.fst Z.hom ιV := by simp only [← Category.assoc, hpa]
    _ = p ≫ (w ≫ pullback.fst (pullback.snd Z.hom ιV) j) ≫ pullback.fst Z.hom ιV := by
        rw [hnat]
    _ = p ≫ u := by simp only [w, v, pullback.lift_fst]
    _ = _ := by simp only [u, ← Category.assoc, hlift]

/-- The preimage of a dense open under an open map is dense: base change of a dense open
immersion along an open morphism is dominant. -/
private lemma isDominant_pullback_fst_opens_ι_of_isOpenMap {X T : Scheme.{u}} (q : T ⟶ X)
    (hq : IsOpenMap q) (U : X.Opens) (hU : Dense (U : Set X)) :
    IsDominant (pullback.fst q U.ι) := by
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
  exact hU.preimage hq

/-- Glueing the extensions over the members of an open cover. Let `U ⊆ X` be a dense open, `𝒱`
an open cover of `X`, `pY : Y ⟶ X` étale and `pZ : Z ⟶ X` finite étale, and
`φ : Y ×_X U ⟶ Z ×_X U`. If for every member `V` of `𝒱` there is a morphism `Y ×_X V ⟶ Z` over
`X` agreeing with `φ` on every part of `Y ×_X V` lying over `U`, then there is a morphism
`Y ⟶ Z` over `X` agreeing with `φ` on `Y ×_X U`. -/
private lemma exists_hom_of_forall_openCover {X Y Z : Scheme.{u}} (U : X.Opens)
    (hU : Dense (U : Set X)) (𝒱 : X.OpenCover) (pY : Y ⟶ X) [Etale pY] (pZ : Z ⟶ X)
    [IsFinite pZ] [Etale pZ] (φ : pullback pY U.ι ⟶ pullback pZ U.ι)
    (t : ∀ i, pullback pY (𝒱.f i) ⟶ Z) (ht : ∀ i, t i ≫ pZ = pullback.snd pY (𝒱.f i) ≫ 𝒱.f i)
    (hext : ∀ (i) {W : Scheme.{u}} (a : W ⟶ pullback pY (𝒱.f i)) (b : W ⟶ U)
      (h : (a ≫ pullback.fst pY (𝒱.f i)) ≫ pY = b ≫ U.ι),
      a ≫ t i = pullback.lift (a ≫ pullback.fst pY (𝒱.f i)) b h ≫ φ ≫ pullback.fst pZ U.ι) :
    ∃ g : Y ⟶ Z, g ≫ pZ = pY ∧ pullback.fst pY U.ι ≫ g = φ ≫ pullback.fst pZ U.ι := by
  let 𝒰 : Y.OpenCover := 𝒱.pullback₁ pY
  -- the local extensions agree on overlaps
  have hcompat : ∀ a b, pullback.fst (pullback.fst pY (𝒱.f a)) (pullback.fst pY (𝒱.f b)) ≫ t a =
      pullback.snd (pullback.fst pY (𝒱.f a)) (pullback.fst pY (𝒱.f b)) ≫ t b := by
    intro a b
    let r₁ := pullback.fst (pullback.fst pY (𝒱.f a)) (pullback.fst pY (𝒱.f b))
    let r₂ := pullback.snd (pullback.fst pY (𝒱.f a)) (pullback.fst pY (𝒱.f b))
    have hcond : r₁ ≫ pullback.fst pY (𝒱.f a) = r₂ ≫ pullback.fst pY (𝒱.f b) :=
      pullback.condition
    let q := r₁ ≫ pullback.fst pY (𝒱.f a) ≫ pY
    have := isDominant_pullback_fst_opens_ι_of_isOpenMap q q.isOpenMap U hU
    refine eq_of_isDominant_of_finiteEtale pZ ?_ (pullback.fst q U.ι) ?_
    · rw [Category.assoc, Category.assoc, ht, ht, ← pullback.condition, ← pullback.condition,
        ← Category.assoc, ← Category.assoc, hcond]
    · have h₁ : ((pullback.fst q U.ι ≫ r₁) ≫ pullback.fst pY (𝒱.f a)) ≫ pY =
          pullback.snd q U.ι ≫ U.ι := by
        rw [← pullback.condition]
        simp only [q, Category.assoc]
      have h₂ : ((pullback.fst q U.ι ≫ r₂) ≫ pullback.fst pY (𝒱.f b)) ≫ pY =
          pullback.snd q U.ι ≫ U.ι := by
        rw [← h₁]
        simp only [Category.assoc, reassoc_of% hcond]
      rw [← Category.assoc, ← Category.assoc, hext a _ _ h₁, hext b _ _ h₂]
      congr 1
      apply pullback.hom_ext
      · rw [pullback.lift_fst, pullback.lift_fst, Category.assoc, Category.assoc, hcond]
      · rw [pullback.lift_snd, pullback.lift_snd]
  let g : Y ⟶ Z := 𝒰.glueMorphisms t hcompat
  have hgι : ∀ i, pullback.fst pY (𝒱.f i) ≫ g = t i := fun i => 𝒰.ι_glueMorphisms t hcompat i
  refine ⟨g, 𝒰.hom_ext _ _ fun i => ?_, ?_⟩
  · show pullback.fst pY (𝒱.f i) ≫ g ≫ pZ = pullback.fst pY (𝒱.f i) ≫ pY
    rw [reassoc_of% (hgι i)]
    exact (ht i).trans pullback.condition.symm
  -- the glued morphism restricts to `φ` over `U`
  let 𝒲 : (pullback pY U.ι).OpenCover := 𝒰.pullback₁ (pullback.fst pY U.ι)
  refine 𝒲.hom_ext _ _ fun (i : 𝒱.I₀) => ?_
  let c₁ := pullback.fst (pullback.fst pY U.ι) (pullback.fst pY (𝒱.f i))
  let c₂ := pullback.snd (pullback.fst pY U.ι) (pullback.fst pY (𝒱.f i))
  have hc : c₁ ≫ pullback.fst pY U.ι = c₂ ≫ pullback.fst pY (𝒱.f i) := pullback.condition
  show c₁ ≫ pullback.fst pY U.ι ≫ g = c₁ ≫ φ ≫ pullback.fst pZ U.ι
  have hW : (c₂ ≫ pullback.fst pY (𝒱.f i)) ≫ pY = (c₁ ≫ pullback.snd pY U.ι) ≫ U.ι := by
    rw [← hc, Category.assoc, Category.assoc, pullback.condition]
  have hl : pullback.lift (c₂ ≫ pullback.fst pY (𝒱.f i)) (c₁ ≫ pullback.snd pY U.ι) hW = c₁ :=
    pullback.hom_ext (by rw [pullback.lift_fst, hc]) (by rw [pullback.lift_snd])
  rw [← Category.assoc, hc, Category.assoc, hgι, hext i _ _ hW, hl]

/-! ### Fullness is local on the base -/

/-- **Fullness of restriction to a dense open is local on `X`.** Let `U ⊆ X` be a dense open and
`𝒱` an open cover of `X`. If for every member `V ⟶ X` of `𝒱` base change of finite étale covers
from `V` to the preimage of `U` in `V` is full, then base change of finite étale covers along
`U ⟶ X` is full.

On each member the morphism of restricted covers extends; the extensions agree on overlaps
because they agree over the preimage of `U`, which is dense there (Stacks 0BQE), and so they glue
along the cover of the source by its parts over the members of `𝒱`. -/
theorem full_finiteEtaleBaseChange_of_openCover {X : Scheme.{u}} (U : X.Opens)
    (hU : Dense (U : Set X)) (𝒱 : X.OpenCover)
    (H : ∀ i, (finiteEtaleBaseChange ((𝒱.f i) ⁻¹ᵁ U).ι).Full) :
    (finiteEtaleBaseChange U.ι).Full := by
  constructor
  intro Y Z φ
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  have : IsFinite Z.hom := Z.prop.1
  have : Etale Z.hom := Z.prop.2
  let φl : pullback Y.hom U.ι ⟶ pullback Z.hom U.ι := φ.left
  have hφ : φl ≫ pullback.snd Z.hom U.ι = pullback.snd Y.hom U.ι := MorphismProperty.Over.w φ
  choose t ht hext using fun i =>
    have := H i
    exists_hom_of_full_finiteEtaleBaseChange (isPullback_morphismRestrict (𝒱.f i) U) Y Z φl hφ
  obtain ⟨g, hg, hgU⟩ := exists_hom_of_forall_openCover U hU 𝒱 Y.hom Z.hom φl t ht hext
  refine ⟨MorphismProperty.Over.homMk g hg, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · exact (finiteEtaleBaseChange_map_left_fst U.ι _).trans hgU
  · show _ = φl ≫ pullback.snd Z.hom U.ι
    rw [hφ]
    exact MorphismProperty.Over.w _

/-- **Full faithfulness of restriction to a dense open is local on `X`.** Let `U ⊆ X` be a dense
open and `𝒱` an open cover of `X`. If for every member `V ⟶ X` of `𝒱` base change of finite étale
covers from `V` to the preimage of `U` in `V` is fully faithful, then so is base change of finite
étale covers along `U ⟶ X`. Faithfulness holds because `U` is dense (Stacks 0BQE); fullness is
`AlgebraicGeometry.full_finiteEtaleBaseChange_of_openCover`. -/
theorem nonempty_fullyFaithful_finiteEtaleBaseChange_of_openCover {X : Scheme.{u}}
    (U : X.Opens) (hU : Dense (U : Set X)) (𝒱 : X.OpenCover)
    (H : ∀ i, Nonempty (finiteEtaleBaseChange ((𝒱.f i) ⁻¹ᵁ U).ι).FullyFaithful) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := by
  have : IsDominant U.ι := Opens.isDominant_ι hU
  have : (finiteEtaleBaseChange U.ι).Faithful := faithful_finiteEtaleBaseChange_of_isDominant U.ι
  have : (finiteEtaleBaseChange U.ι).Full :=
    full_finiteEtaleBaseChange_of_openCover U hU 𝒱 fun i => (Classical.choice (H i)).full
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

/-! ### The local hypothesis up to isomorphism -/

/-- **The local hypothesis of [Stacks, Tag 0BQF] is invariant under isomorphism.** If the
punctured spectrum of every strict henselization of the local ring `R` is connected, the same
holds for every local ring isomorphic to `R`: a strict henselization of `R'` is one of `R` along
the isomorphism (`Stacks.StrictHenselization.exists_isStrictHenselization_of_ringEquiv`), and
the punctured spectrum does not depend on the algebra structure. -/
theorem IsConnectedPuncturedStrictHenselization.of_ringEquiv {R R' : Type u} [CommRing R]
    [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (e : R ≃+* R')
    (h : IsConnectedPuncturedStrictHenselization R) :
    IsConnectedPuncturedStrictHenselization R' := by
  intro κsep _ _ _ Rsh _ _ _ hsh
  obtain ⟨_, _, _, ⟨hsh'⟩, -⟩ :=
    Stacks.StrictHenselization.exists_isStrictHenselization_of_ringEquiv hsh e.symm
  exact h κsep Rsh hsh'

/-! ### Tag 0BQF for a locally Noetherian scheme -/

/-- **[Stacks, Tag 0BQF] for a locally Noetherian scheme.** Let `X` be a locally Noetherian
scheme and `U ⊆ X` a dense open, and suppose that for every point `x` of `X` outside `U` the
punctured spectrum of every strict henselization of `𝒪_{X, x}` is connected. Then base change of
finite étale covers along `U ⟶ X` is fully faithful.

The source asks for the underlying space of `X` to be Noetherian; that case is
`AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_dense_of_noetherianSpace`. Here it is
applied on each member of an affine open cover of `X`, which is Noetherian, at the preimage of
`U`; the local hypothesis is transported along the isomorphisms of stalks of the open immersion,
and the conclusions glue by `AlgebraicGeometry.nonempty_fullyFaithful_finiteEtaleBaseChange_of_`
`openCover`. -/
@[sga "7 II 2.3.1" "partial"]
theorem fullyFaithful_finiteEtaleBaseChange_of_dense_of_isLocallyNoetherian
    (X : Scheme.{u}) (U : X.Opens) [IsLocallyNoetherian X] (hU : Dense (U : Set X))
    (hconn : ∀ x : X, x ∉ U →
      IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x)) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := by
  refine nonempty_fullyFaithful_finiteEtaleBaseChange_of_openCover U hU X.affineCover fun i => ?_
  let f := X.affineCover.f i
  have : IsLocallyNoetherian (X.affineCover.X i) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherian (X.affineCover.X i) := {}
  refine fullyFaithful_finiteEtaleBaseChange_of_dense_of_noetherianSpace _ (f ⁻¹ᵁ U)
    (hU.preimage f.isOpenEmbedding.isOpenMap) fun y hy => ?_
  exact (hconn (f y) hy).of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv

end AlgebraicGeometry

end
