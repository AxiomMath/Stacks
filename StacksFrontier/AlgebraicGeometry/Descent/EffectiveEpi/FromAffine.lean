module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Topology.Maps.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.AffineBase

/-!
# Universal effective epimorphisms of schemes from affine families

A family of affine morphisms which is universally effective epimorphic among affine schemes
is universally effective epimorphic among all schemes, provided its base change to every
affine scheme is submersive on underlying topological spaces.

## Main results

* `AlgebraicGeometry.isUniversalEffectiveEpiFamily_of_affine_of_submersive` extends
  universal effective epimorphy from affine schemes to schemes.

## Implementation notes

The coproduct of the underlying spaces of the base-changed family is expressed as a
dependent sum, and its map to the affine base is the family of second projections. The
submersiveness hypothesis uses `Topology.IsQuotientMap`, the Stacks notion of a surjective
map inducing the quotient topology.

Given a compatible family of morphisms out of the base-changed family, submersiveness
produces the underlying continuous map of the descended morphism. Its scheme structure is
then built locally: over an affine open of the base which maps into an affine open of the
target, the affine case applies, and the resulting local morphisms agree on overlaps because
each is determined by the same continuous map, so they glue.

## References

* [Stacks Project, Lemma 35.13.5 (Tag 0EUD)](https://stacks.math.columbia.edu/tag/0EUD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

private theorem exists_continuousMap_of_isQuotientMap
    {ι : Type w} {A : ι → Type u} [∀ i, TopologicalSpace (A i)]
    {B C : Type u} [TopologicalSpace B] [TopologicalSpace C]
    (q : (Σ i, A i) → B) (hq : Topology.IsQuotientMap q)
    (g : ∀ i, A i → C) (hg : ∀ i, Continuous (g i))
    (hcompat : ∀ x y, q x = q y → g x.1 x.2 = g y.1 y.2) :
    ∃ h : B → C, Continuous h ∧ ∀ i x, h (q ⟨i, x⟩) = g i x := by
  let G : C((Σ i, A i), C) := ⟨fun x => g x.1 x.2, continuous_sigma hg⟩
  let Q : C((Σ i, A i), B) := ⟨q, hq.continuous⟩
  have hc : Function.FactorsThrough G Q := fun ⦃x y⦄ h => hcompat x y h
  let H := Topology.IsQuotientMap.lift (f := Q) hq G hc
  exact ⟨H, H.continuous, fun i x => congrArg (fun K : C((Σ i, A i), C) => K ⟨i, x⟩)
    (Topology.IsQuotientMap.lift_comp (f := Q) hq G hc)⟩

private theorem existsUnique_morphism_to_affine
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h_affine : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f)
    (Y : Scheme.{u}) [IsAffine Y]
    (g : Y ⟶ AffineScheme.forgetToScheme.obj X)
    (T : Scheme.{u}) [IsAffine T]
    (φ : ∀ i, pullback (AffineScheme.forgetToScheme.map (f i)) g ⟶ T)
    (hφ : ∀ i j (Z : Scheme.{u})
      (a : Z ⟶ pullback (AffineScheme.forgetToScheme.map (f i)) g)
      (b : Z ⟶ pullback (AffineScheme.forgetToScheme.map (f j)) g),
      IsPullback a b (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g)
        (pullback.snd (AffineScheme.forgetToScheme.map (f j)) g) →
      a ≫ φ i = b ≫ φ j) :
    ∃! t : Y ⟶ T, ∀ i,
      pullback.snd (AffineScheme.forgetToScheme.map (f i)) g ≫ t = φ i := by
  let P i := pullback (AffineScheme.forgetToScheme.map (f i)) g
  let π i := pullback.snd (AffineScheme.forgetToScheme.map (f i)) g
  have hP i : IsAffine (P i) := by
    have hg : IsAffineHom g :=
      @isAffineHom_of_isAffine Y X.obj g ‹IsAffine Y›
        (AlgebraicGeometry.isAffine_affineScheme X)
    exact @IsAffine.of_isPullback (U i).obj Y X.obj (P i)
      (pullback.fst (AffineScheme.forgetToScheme.map (f i)) g)
      (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g)
      (AffineScheme.forgetToScheme.map (f i)) g
      (AlgebraicGeometry.isAffine_affineScheme (U i)) hg
      (IsPullback.of_hasPullback (AffineScheme.forgetToScheme.map (f i)) g)
  let A i : AffineScheme := AffineScheme.mk (P i) (hP i)
  let q i : A i ⟶ AffineScheme.of Y := haveI := hP i; AffineScheme.ofHom (π i)
  let p i : A i ⟶ U i := haveI := hP i
    AffineScheme.ofHom (pullback.fst (AffineScheme.forgetToScheme.map (f i)) g)
  let g' : AffineScheme.of Y ⟶ X := AffineScheme.ofHom g
  let T' : AffineScheme := AffineScheme.of T
  let φ' i : A i ⟶ T' := haveI := hP i; AffineScheme.ofHom (φ i)
  have hq i : AffineScheme.forgetToScheme.map (q i) = π i := rfl
  have hφi i : AffineScheme.forgetToScheme.map (φ' i) = φ i := rfl
  have hobjA i : AffineScheme.forgetToScheme.obj (A i) = P i := rfl
  have hobjY : AffineScheme.forgetToScheme.obj (AffineScheme.of Y) = Y := rfl
  have hobjT : AffineScheme.forgetToScheme.obj T' = T := rfl
  have hpb i : IsPullback (q i) (p i) g' (f i) :=
    IsPullback.of_map_of_faithful (F := AffineScheme.forgetToScheme.{u})
      (IsPullback.of_hasPullback (AffineScheme.forgetToScheme.map (f i)) g).flip
  have hφ' : ∀ (i j : I) (Z : AffineScheme.{u}) (a : Z ⟶ A i) (b : Z ⟶ A j),
      IsPullback a b (q i) (q j) → a ≫ φ' i = b ≫ φ' j := by
    intro i j Z a b hab
    have hab' := IsPullback.map AffineScheme.forgetToScheme.{u} hab
    cases hobjA i
    cases hobjA j
    cases hobjY
    have hab'' : IsPullback (AffineScheme.forgetToScheme.map a)
        (AffineScheme.forgetToScheme.map b) (π i) (π j) := by
      rwa [hq i, hq j] at hab'
    exact InducedCategory.hom_ext (hφ i j (AffineScheme.forgetToScheme.obj Z)
      (AffineScheme.forgetToScheme.map a) (AffineScheme.forgetToScheme.map b) hab'')
  obtain ⟨t, ht, htuniq⟩ :=
    (h_affine.2 g' A q p hpb).2 T' φ' hφ'
  refine ⟨AffineScheme.forgetToScheme.map t, ?_, ?_⟩
  · intro i
    have hti := congrArg AffineScheme.forgetToScheme.map (ht i)
    cases hobjA i
    cases hobjY
    cases hobjT
    simp only [Functor.map_comp, hq i, hφi i] at hti
    exact hti
  · intro t' ht'
    have htAff : ∀ i, q i ≫ AffineScheme.ofHom t' = φ' i :=
      fun i => InducedCategory.hom_ext (ht' i)
    have heq := htuniq (AffineScheme.ofHom t') htAff
    cases hobjY
    cases hobjT
    exact congrArg (·.hom) heq

private theorem existsUnique_morphism_to_affineOpen
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h_affine : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f)
    (Y : Scheme.{u}) [IsAffine Y]
    (g : Y ⟶ AffineScheme.forgetToScheme.obj X)
    (T : Scheme.{u}) (V : T.affineOpens)
    (φ : ∀ i, pullback (AffineScheme.forgetToScheme.map (f i)) g ⟶ T)
    (hφ : ∀ i j (Z : Scheme.{u})
      (a : Z ⟶ pullback (AffineScheme.forgetToScheme.map (f i)) g)
      (b : Z ⟶ pullback (AffineScheme.forgetToScheme.map (f j)) g),
      IsPullback a b (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g)
        (pullback.snd (AffineScheme.forgetToScheme.map (f j)) g) →
      a ≫ φ i = b ≫ φ j)
    (hq : Topology.IsQuotientMap (fun p : Σ i : I,
      (pullback (AffineScheme.forgetToScheme.map (f i)) g : Scheme.{u}) =>
        (pullback.snd (AffineScheme.forgetToScheme.map (f p.1)) g) p.2))
    (h : Y → T)
    (himage : ∀ y, h y ∈ V.1)
    (hfactor : ∀ i x, h ((pullback.snd (AffineScheme.forgetToScheme.map (f i)) g) x) = φ i x) :
    ∃! t : Y ⟶ T, ∀ i,
      pullback.snd (AffineScheme.forgetToScheme.map (f i)) g ≫ t = φ i := by
  classical
  let P i := pullback (AffineScheme.forgetToScheme.map (f i)) g
  let π i := pullback.snd (AffineScheme.forgetToScheme.map (f i)) g
  let ψ i : P i ⟶ V.1.toScheme :=
    IsOpenImmersion.lift V.1.ι (φ i) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨h (π i x), himage (π i x)⟩, hfactor i x⟩)
  have hψfac (i) : ψ i ≫ V.1.ι = φ i := IsOpenImmersion.lift_fac _ _ _
  have hψ : ∀ (i j : I) (Z : Scheme.{u}) (a : Z ⟶ P i) (b : Z ⟶ P j),
      IsPullback a b (π i) (π j) → a ≫ ψ i = b ≫ ψ j := by
    intro i j Z a b hab
    exact (cancel_mono V.1.ι).mp (by simpa only [Category.assoc, hψfac] using hφ i j Z a b hab)
  obtain ⟨tV, htV, htVuniq⟩ :=
    existsUnique_morphism_to_affine X U f h_affine Y g V.1.toScheme ψ hψ
  refine ⟨tV ≫ V.1.ι, fun i => ?_, fun t' ht' => ?_⟩
  · show π i ≫ (tV ≫ V.1.ι) = φ i
    rw [← Category.assoc, htV i, hψfac i]
  · have hbase : ∀ y, t' y = h y := by
      intro y
      obtain ⟨⟨i, x⟩, rfl⟩ := hq.surjective y
      exact (congrArg (fun k : P i ⟶ T => k x) (ht' i)).trans (hfactor i x).symm
    let tV' : Y ⟶ V.1.toScheme :=
      IsOpenImmersion.lift V.1.ι t' (by
        rintro _ ⟨y, rfl⟩
        refine ⟨⟨t' y, ?_⟩, rfl⟩
        rw [hbase y]
        exact himage y)
    have htV'fac : tV' ≫ V.1.ι = t' := IsOpenImmersion.lift_fac _ _ _
    have htV' : ∀ i, π i ≫ tV' = ψ i := fun i =>
      (cancel_mono V.1.ι).mp (by simpa only [Category.assoc, htV'fac, hψfac] using ht' i)
    rw [← htV'fac, htVuniq tV' htV']

private noncomputable def pullbackBaseChangeMap
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) {Y Z : Scheme.{u}}
    (g : Y ⟶ AffineScheme.forgetToScheme.obj X) (w : Z ⟶ Y) (i : I) :
    pullback (AffineScheme.forgetToScheme.map (f i)) (w ≫ g) ⟶
      pullback (AffineScheme.forgetToScheme.map (f i)) g :=
  pullback.lift
    (pullback.fst (AffineScheme.forgetToScheme.map (f i)) (w ≫ g))
    (pullback.snd (AffineScheme.forgetToScheme.map (f i)) (w ≫ g) ≫ w)
    (pullback.condition.trans (Category.assoc _ _ _).symm)

@[reassoc]
private theorem pullbackBaseChangeMap_fst
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) {Y Z : Scheme.{u}}
    (g : Y ⟶ AffineScheme.forgetToScheme.obj X) (w : Z ⟶ Y) (i : I) :
    pullbackBaseChangeMap X U f g w i ≫
        pullback.fst (AffineScheme.forgetToScheme.map (f i)) g =
      pullback.fst (AffineScheme.forgetToScheme.map (f i)) (w ≫ g) :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem pullbackBaseChangeMap_snd
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) {Y Z : Scheme.{u}}
    (g : Y ⟶ AffineScheme.forgetToScheme.obj X) (w : Z ⟶ Y) (i : I) :
    pullbackBaseChangeMap X U f g w i ≫
        pullback.snd (AffineScheme.forgetToScheme.map (f i)) g =
      pullback.snd (AffineScheme.forgetToScheme.map (f i)) (w ≫ g) ≫ w :=
  pullback.lift_snd _ _ _

private theorem existsUnique_morphism_from_affine_open
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h_affine : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f)
    {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ AffineScheme.forgetToScheme.obj X)
    (T : Scheme.{u})
    (φ : ∀ i, pullback (AffineScheme.forgetToScheme.map (f i)) g ⟶ T)
    (hφ : ∀ i j (Z : Scheme.{u})
      (a : Z ⟶ pullback (AffineScheme.forgetToScheme.map (f i)) g)
      (b : Z ⟶ pullback (AffineScheme.forgetToScheme.map (f j)) g),
      IsPullback a b (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g)
        (pullback.snd (AffineScheme.forgetToScheme.map (f j)) g) →
      a ≫ φ i = b ≫ φ j)
    (h : Y → T)
    (hfactor : ∀ i x,
      h ((pullback.snd (AffineScheme.forgetToScheme.map (f i)) g) x) = φ i x)
    {Z : Scheme.{u}} [IsAffine Z] (w : Z ⟶ Y) (V : T.affineOpens)
    (hq : Topology.IsQuotientMap (fun p : Σ i : I,
      (pullback (AffineScheme.forgetToScheme.map (f i)) (w ≫ g) : Scheme.{u}) =>
        (pullback.snd (AffineScheme.forgetToScheme.map (f p.1)) (w ≫ g)) p.2))
    (himage : ∀ z, h (w z) ∈ V.1) :
    ∃! t : Z ⟶ T, ∀ i,
      pullback.snd (AffineScheme.forgetToScheme.map (f i)) (w ≫ g) ≫ t =
        pullbackBaseChangeMap X U f g w i ≫ φ i := by
  classical
  let gi : Z ⟶ AffineScheme.forgetToScheme.obj X := w ≫ g
  let ri (i : I) := pullbackBaseChangeMap X U f g w i
  let ψ (i : I) := ri i ≫ φ i
  have hpair (i j : I) : pullback.fst
      (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g)
      (pullback.snd (AffineScheme.forgetToScheme.map (f j)) g) ≫ φ i =
      pullback.snd (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g)
      (pullback.snd (AffineScheme.forgetToScheme.map (f j)) g) ≫ φ j :=
    hφ i j _ _ _ (IsPullback.of_hasPullback _ _)
  have hrsnd (i : I) : ri i ≫ pullback.snd (AffineScheme.forgetToScheme.map (f i)) g =
      pullback.snd (AffineScheme.forgetToScheme.map (f i)) gi ≫ w :=
    pullbackBaseChangeMap_snd X U f g w i
  have hψ : ∀ (i j : I) (W : Scheme.{u}) (a : W ⟶
      pullback (AffineScheme.forgetToScheme.map (f i)) gi)
      (b : W ⟶ pullback (AffineScheme.forgetToScheme.map (f j)) gi),
      IsPullback a b
        (pullback.snd (AffineScheme.forgetToScheme.map (f i)) gi)
        (pullback.snd (AffineScheme.forgetToScheme.map (f j)) gi) →
      a ≫ ψ i = b ≫ ψ j := by
    intro i j W a b hab
    have hbase : (a ≫ ri i) ≫ pullback.snd
          (AffineScheme.forgetToScheme.map (f i)) g =
        (b ≫ ri j) ≫ pullback.snd
          (AffineScheme.forgetToScheme.map (f j)) g := by
      simp only [Category.assoc, hrsnd, reassoc_of% hab.w]
    let c := pullback.lift (a ≫ ri i) (b ≫ ri j) hbase
    have hcfst : c ≫ pullback.fst _ _ = a ≫ ri i := pullback.lift_fst _ _ _
    have hcsnd : c ≫ pullback.snd _ _ = b ≫ ri j := pullback.lift_snd _ _ _
    show a ≫ (ri i ≫ φ i) = b ≫ (ri j ≫ φ j)
    rw [← reassoc_of% hcfst, hpair i j, reassoc_of% hcsnd]
  have hfactor' : ∀ i x,
      h (w ((pullback.snd (AffineScheme.forgetToScheme.map (f i)) gi) x)) = ψ i x := by
    intro i x
    have hx := congrArg (fun k : pullback
        (AffineScheme.forgetToScheme.map (f i)) gi ⟶ Y => k x) (hrsnd i)
    change pullback.snd (AffineScheme.forgetToScheme.map (f i)) g (ri i x) =
      w ((pullback.snd (AffineScheme.forgetToScheme.map (f i)) gi) x) at hx
    show h (w ((pullback.snd (AffineScheme.forgetToScheme.map (f i)) gi) x)) =
      φ i (ri i x)
    rw [← hx]
    exact hfactor i (ri i x)
  exact existsUnique_morphism_to_affineOpen X U f h_affine Z gi T V ψ hψ
    hq (fun z => h (w z)) himage hfactor'

private theorem pullbackBaseChangeMap_restrict
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) {Y Z W T : Scheme.{u}} (g : Y ⟶ AffineScheme.forgetToScheme.obj X)
    (φ : ∀ i, pullback (AffineScheme.forgetToScheme.map (f i)) g ⟶ T)
    (v : W ⟶ Z) (w : Z ⟶ Y) (u : W ⟶ Y) (hv : v ≫ w = u) (s : Z ⟶ T)
    (hs : ∀ k, pullback.snd (AffineScheme.forgetToScheme.map (f k)) (w ≫ g) ≫ s =
      pullbackBaseChangeMap X U f g w k ≫ φ k) (k : I) :
    pullback.snd (AffineScheme.forgetToScheme.map (f k)) (u ≫ g) ≫ v ≫ s =
      pullbackBaseChangeMap X U f g u k ≫ φ k := by
  subst hv
  have hd : pullback.fst (AffineScheme.forgetToScheme.map (f k)) ((v ≫ w) ≫ g) ≫
      AffineScheme.forgetToScheme.map (f k) =
      (pullback.snd (AffineScheme.forgetToScheme.map (f k)) ((v ≫ w) ≫ g) ≫ v) ≫ w ≫ g := by
    rw [pullback.condition]
    simp only [Category.assoc]
  obtain ⟨d, hdfst, hdsnd⟩ : ∃ d : pullback (AffineScheme.forgetToScheme.map (f k))
      ((v ≫ w) ≫ g) ⟶ pullback (AffineScheme.forgetToScheme.map (f k)) (w ≫ g),
      d ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        d ≫ pullback.snd (AffineScheme.forgetToScheme.map (f k)) (w ≫ g) =
          pullback.snd (AffineScheme.forgetToScheme.map (f k)) ((v ≫ w) ≫ g) ≫ v :=
    ⟨pullback.lift _ _ hd, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hdr : d ≫ pullbackBaseChangeMap X U f g w k =
      pullbackBaseChangeMap X U f g (v ≫ w) k := by
    apply pullback.hom_ext
    · rw [Category.assoc d, pullbackBaseChangeMap_fst, pullbackBaseChangeMap_fst, hdfst]
    · rw [Category.assoc d, pullbackBaseChangeMap_snd, pullbackBaseChangeMap_snd,
        ← Category.assoc d, hdsnd]
      exact Category.assoc _ _ _
  rw [← reassoc_of% hdsnd, hs, reassoc_of% hdr]

private theorem cover_compat_of_continuous
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h_affine : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f)
    (h_submersive : ∀ (Y : Scheme.{u}) [IsAffine Y] (g : Y ⟶ X.obj),
      Topology.IsQuotientMap
        (fun p : Σ i : I,
            (pullback (AffineScheme.forgetToScheme.map (f i)) g : Scheme.{u}) =>
          (pullback.snd (AffineScheme.forgetToScheme.map (f p.1)) g).base p.2))
    {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ AffineScheme.forgetToScheme.obj X)
    (T : Scheme.{u})
    (φ : ∀ i, pullback (AffineScheme.forgetToScheme.map (f i)) g ⟶ T)
    (hφ : ∀ i j (Z : Scheme.{u})
      (a : Z ⟶ pullback (AffineScheme.forgetToScheme.map (f i)) g)
      (b : Z ⟶ pullback (AffineScheme.forgetToScheme.map (f j)) g),
      IsPullback a b (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g)
        (pullback.snd (AffineScheme.forgetToScheme.map (f j)) g) →
      a ≫ φ i = b ≫ φ j)
    (h : Y → T) (hh : Continuous h)
    (hfactor : ∀ i x,
      h ((pullback.snd (AffineScheme.forgetToScheme.map (f i)) g) x) = φ i x)
    (𝒰 : Y.OpenCover) (t : ∀ i, 𝒰.X i ⟶ T)
    (ht : ∀ i k, pullback.snd (AffineScheme.forgetToScheme.map (f k)) (𝒰.f i ≫ g) ≫ t i =
      pullbackBaseChangeMap X U f g (𝒰.f i) k ≫ φ k) (i j : 𝒰.I₀) :
    pullback.fst (𝒰.f i) (𝒰.f j) ≫ t i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ t j := by
  apply Scheme.hom_ext_of_forall
  intro z
  let R : Scheme := pullback (𝒰.f i) (𝒰.f j)
  let ρ : R ⟶ Y := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i
  let c : C(R, T) := ⟨fun x => h (ρ x), hh.comp ρ.continuous⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (h (ρ z))) isOpen_univ
  let O : R.Opens := V.comap c
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWO⟩ :=
    R.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ O from hzV) O.2
  let W' : R.Opens := W
  have : IsAffine W'.toScheme := hW
  let ui : W'.toScheme ⟶ 𝒰.X i := W'.ι ≫ pullback.fst (𝒰.f i) (𝒰.f j)
  let uj : W'.toScheme ⟶ 𝒰.X j := W'.ι ≫ pullback.snd (𝒰.f i) (𝒰.f j)
  have himage : ∀ x : W'.toScheme, h ((ui ≫ 𝒰.f i) x) ∈ V := fun x => by
    have hx : c (W'.ι x) ∈ V := (congrArg (fun y => c y ∈ V) (W'.ι_apply x)).mpr (hWO x.2)
    simpa [c, ρ, ui, R] using hx
  obtain ⟨tW, -, htW⟩ := existsUnique_morphism_from_affine_open X U f h_affine g T φ hφ h
    hfactor (ui ≫ 𝒰.f i) ⟨V, hV⟩ (h_submersive W'.toScheme ((ui ≫ 𝒰.f i) ≫ g)) himage
  refine ⟨W', hzW, show ui ≫ t i = uj ≫ t j from (htW _ ?_).trans (htW _ ?_).symm⟩
  · exact pullbackBaseChangeMap_restrict X U f g φ ui (𝒰.f i) _ rfl (t i) (ht i)
  · exact pullbackBaseChangeMap_restrict X U f g φ uj (𝒰.f j) _
      (by simp [ui, uj, pullback.condition]) (t j) (ht j)

private theorem pullback_snd_comp_eq_of_cover
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X) {Y T : Scheme.{u}} (g : Y ⟶ AffineScheme.forgetToScheme.obj X)
    (φ : ∀ i, pullback (AffineScheme.forgetToScheme.map (f i)) g ⟶ T)
    (𝒰 : Y.OpenCover) (t : ∀ i, 𝒰.X i ⟶ T)
    (ht : ∀ i k, pullback.snd (AffineScheme.forgetToScheme.map (f k)) (𝒰.f i ≫ g) ≫ t i =
      pullbackBaseChangeMap X U f g (𝒰.f i) k ≫ φ k)
    (s : Y ⟶ T) (hs : ∀ k, 𝒰.f k ≫ s = t k) (i : I) :
    pullback.snd (AffineScheme.forgetToScheme.map (f i)) g ≫ s = φ i := by
  apply Scheme.Cover.hom_ext
    (𝒰.pullback₁ (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g))
  intro (k : 𝒰.I₀)
  show pullback.fst (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g) (𝒰.f k) ≫
      pullback.snd (AffineScheme.forgetToScheme.map (f i)) g ≫ s =
    pullback.fst (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g) (𝒰.f k) ≫ φ i
  obtain ⟨e, hefst, hesnd⟩ : ∃ e : pullback (pullback.snd
      (AffineScheme.forgetToScheme.map (f i)) g) (𝒰.f k) ⟶
      pullback (AffineScheme.forgetToScheme.map (f i)) (𝒰.f k ≫ g),
      e ≫ pullback.fst (AffineScheme.forgetToScheme.map (f i)) (𝒰.f k ≫ g) =
          pullback.fst (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g) (𝒰.f k) ≫
            pullback.fst (AffineScheme.forgetToScheme.map (f i)) g ∧
        e ≫ pullback.snd (AffineScheme.forgetToScheme.map (f i)) (𝒰.f k ≫ g) =
          pullback.snd (pullback.snd (AffineScheme.forgetToScheme.map (f i)) g) (𝒰.f k) :=
    ⟨pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by simp [pullback.condition, pullback.condition_assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have he : e ≫ pullbackBaseChangeMap X U f g (𝒰.f k) i = pullback.fst _ _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackBaseChangeMap_fst, hefst]
    · rw [Category.assoc, pullbackBaseChangeMap_snd, ← Category.assoc, hesnd]
      exact pullback.condition.symm
  rw [pullback.condition_assoc, hs, ← reassoc_of% hesnd, ht k i, reassoc_of% he]

/-- **Stacks Project, Tag 0EUD.** A universally effective epimorphic family of affine
schemes whose every affine base change is submersive is a universally effective
epimorphic family in schemes. -/
@[stacks 0EUD]
public theorem isUniversalEffectiveEpiFamily_of_affine_of_submersive
    {I : Type w} (X : AffineScheme.{u}) (U : I → AffineScheme.{u})
    (f : ∀ i, U i ⟶ X)
    (h_affine : StacksEffectiveEpi.IsUniversalEffectiveEpiFamily U f)
    (h_submersive : ∀ (Y : Scheme.{u}) [IsAffine Y] (g : Y ⟶ X.obj),
      Topology.IsQuotientMap
        (fun p : Σ i : I,
            (pullback (AffineScheme.forgetToScheme.map (f i)) g : Scheme.{u}) =>
          (pullback.snd (AffineScheme.forgetToScheme.map (f p.1)) g).base p.2)) :
    StacksEffectiveEpi.IsUniversalEffectiveEpiFamily
      (fun i => (U i).obj) (fun i => AffineScheme.forgetToScheme.map (f i)) := by
  apply isUniversalEffectiveEpiFamily_of_affine_baseChange
    (X' := fun i => (U i).obj)
    (f := fun i => AffineScheme.forgetToScheme.map (f i))
  intro Y hY g
  let P : I → Scheme.{u} := fun i =>
    pullback (AffineScheme.forgetToScheme.map (f i)) g
  let π : ∀ i, P i ⟶ Y := fun i =>
    pullback.snd (AffineScheme.forgetToScheme.map (f i)) g
  refine ⟨fun _ => inferInstance, fun T φ hφ => ?_⟩
  let q : (Σ i, P i) → Y := fun p => (π p.1).base p.2
  have hcompat : ∀ x y : Σ i, P i, q x = q y → φ x.1 x.2 = φ y.1 y.2 := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
    have hz := congrArg (fun k : pullback (π i) (π j) ⟶ T => k z)
      (hφ i j _ _ _ (IsPullback.of_hasPullback (π i) (π j)))
    change (φ i) ((pullback.fst (π i) (π j)) z) =
      (φ j) ((pullback.snd (π i) (π j)) z) at hz
    rwa [hz₁, hz₂] at hz
  obtain ⟨h, hh, hfactor⟩ := exists_continuousMap_of_isQuotientMap
    q (h_submersive Y g) (fun i => (φ i).base.hom) (fun i => (φ i).continuous) hcompat
  -- The continuous map `h` is the underlying map of the descended morphism.
  -- Construct its morphism structure locally on affine opens of `Y` and `T`.
  let 𝒰 : Y.OpenCover := Y.openCoverOfIsOpenCover _ <|
    Y.isBasis_affineOpens.isOpenCover_mem_and_le
      (T.isBasis_affineOpens.isOpenCover.comap ⟨h, hh⟩)
  have hlocal (i : 𝒰.I₀) : ∃! t : 𝒰.X i ⟶ T, ∀ j,
      pullback.snd (AffineScheme.forgetToScheme.map (f j)) (𝒰.f i ≫ g) ≫ t =
        pullbackBaseChangeMap X U f g (𝒰.f i) j ≫ φ j := by
    have : IsAffine (𝒰.X i) := i.2.1
    exact existsUnique_morphism_from_affine_open X U f h_affine g T φ hφ h hfactor
      (Z := 𝒰.X i) (𝒰.f i) i.1.2 (h_submersive (𝒰.X i) (𝒰.f i ≫ g))
      (fun y => i.2.2 (show (𝒰.f i) y ∈ (i.1.1 : Y.Opens) from y.2))
  choose t ht htuniq using hlocal
  have hglue := cover_compat_of_continuous X U f h_affine h_submersive g T φ hφ h hh
    hfactor 𝒰 t ht
  refine ⟨𝒰.glueMorphisms t hglue, pullback_snd_comp_eq_of_cover X U f g φ 𝒰 t ht _
    (𝒰.ι_glueMorphisms t hglue), fun t' ht' => ?_⟩
  apply Scheme.Cover.hom_ext 𝒰
  intro k
  rw [𝒰.ι_glueMorphisms]
  refine htuniq k _ fun j => ?_
  rw [← pullbackBaseChangeMap_snd_assoc X U f g (𝒰.f k) j]
  exact _ ≫= ht' j

end AlgebraicGeometry
