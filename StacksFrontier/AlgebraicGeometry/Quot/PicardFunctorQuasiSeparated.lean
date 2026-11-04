module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsom
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.IsPullbackPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFiniteCoverDescent

/-!
# Quasi-separatedness of an algebraic space representing `Pic_{X/B}` (towards Stacks 0DNI)

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S`, and let `p : H ⟶ B` be an algebraic
space over `B` whose functor of points over `B` is identified with the relative Picard functor
`Pic_{X/B}`. The first half of Stacks 0DNI says that `p` is quasi-separated, i.e. that the
diagonal `H ⟶ H ×_B H` is quasi-compact. The source deduces it from Stacks 0DMF, whose
quasi-compactness half comes from Stacks 0DMA (the diagonal of `Picardstack_{X/B}` over `B` is
affine), the gerbe `Picardstack_{X/B} ⟶ Pic_{X/B}` of Stacks 0DME and Morphisms of Stacks,
Lemma 0DQL. The immersion half of 0DMF (Stacks 0D2D) is not needed.

## The argument

The diagonal of `Picardstack_{X/B}` over `B`, read at a point `(L, N)` over a scheme `T`, is the
relative Isom functor `Isom(L, N)` of `X_T ⟶ T` (Stacks 08K7) of the two invertible modules on
`X_T`. Here it enters only through the *Isom input* `hIsom`: over an affine test scheme `T`,
`Isom(L, N)` is an algebraic space affine over `T` (Stacks 08K9 for `X_T ⟶ T`, which is what
Stacks 0DMA, through Stacks 0DLY, reads at the point `(L, N)`). It is then represented by an
affine scheme `W ⟶ T`, through which a morphism of test schemes `g : T' ⟶ T` factors exactly
when `g^*L ≅ g^*N` on `X_{T'}`; only the quasi-compactness of `W` is used.

The proof of Stacks 0DQL is carried out on the equalizers of points of `Pic_{X/B}`:

* The base change of the diagonal of `H` along a point `h_T ⟶ H ×_B H` is the equalizer `E` of
  two points `x, y ∈ Pic_{X/B}(T)`, represented by a monomorphism of schemes `j : P ⟶ T`
  (the diagonal of an algebraic space is representable). It is to be shown that `j⁻¹(U)` is
  quasi-compact for every affine open `U ⊆ T`.
* fppf locally on `T`, `x` and `y` are the classes of invertible modules `L`, `N` (this is
  condition (2)(a) of the gerbe Stacks 0DME); over an affine `U` take finitely many affine
  `V_i ⟶ U` of the covering, jointly surjective.
* Over such a `V` the Isom input gives a quasi-compact `W ⟶ V` mapping into the equalizer, since
  isomorphic modules have the same class; conversely, at a point of the equalizer the two
  modules are fppf locally isomorphic (condition (2)(b) of Stacks 0DME, here the local
  injectivity of `Pic(X_T) ⟶ Pic_{X/B}(T)`), so every point of the equalizer comes from `W`.
* Hence `j⁻¹(U)` is the union of the images of finitely many quasi-compact `W_i`.

## Main definitions

* `AlgebraicGeometry.Space.PicardSituation.isomHomSituation`: the relative Hom situation of two
  invertible modules on `X_T`, over `T`; its relative Isom functor is `Isom(L, N)`.

## Main results

* `isQuasiSeparated_of_represents_of_isAffineAlgebraicSpaceOver_isomFunctor`, in the namespace
  `AlgebraicGeometry.Space.PicardSituation`: an algebraic space representing `Pic_{X/B}` is
  quasi-separated over `B`, given that `Isom(L, N)` is an algebraic space affine over every
  affine test scheme `T`. Not registered.

## Implementation notes

This follows an earlier, unpublished argument
(`isQuasiCompact_diagonal_of_represents_of_isLocallySeparated`), with two changes: the conclusion
of Stacks 0D2D (an immersive diagonal) is not used, the representability of the diagonal coming
from `H` being an algebraic space; and the conclusion of Stacks 0DMA is replaced by the Isom
input above, read directly on invertible modules rather than through the 2-fibre product of the
Picard stack.

## References

* [Stacks Project, Tag 0DNI](https://stacks.math.columbia.edu/tag/0DNI)
* [Stacks Project, Tag 0DMF](https://stacks.math.columbia.edu/tag/0DMF)
* [Stacks Project, Tag 0DMA](https://stacks.math.columbia.edu/tag/0DMA)
* [Stacks Project, Tag 0DME](https://stacks.math.columbia.edu/tag/0DME)
* [Stacks Project, Tag 0DQL](https://stacks.math.columbia.edu/tag/0DQL)
* [Stacks Project, Tag 08K7](https://stacks.math.columbia.edu/tag/08K7)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PicardSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : PicardSituation B S hS)

/-- A pullback square whose right-hand vertical leg is a representable morphism lets one lift
compatible representable test objects. -/
private theorem exists_comp_eq_of_isPullback_yoneda {C : Type*} [Category C]
    {b c W : C} {X Z : Cᵒᵖ ⥤ Type _} {fst : yoneda.obj b ⟶ X} {snd : b ⟶ c} {f : X ⟶ Z}
    {g : yoneda.obj c ⟶ Z} (hpb : IsPullback fst (yoneda.map snd) f g) (u : yoneda.obj W ⟶ X)
    (v : W ⟶ c) (h : u ≫ f = yoneda.map v ≫ g) : ∃ l : W ⟶ b, l ≫ snd = v := by
  refine ⟨Yoneda.fullyFaithful.preimage (hpb.lift _ _ h), yoneda.map_injective ?_⟩
  rw [Functor.map_comp, Yoneda.fullyFaithful.map_preimage]
  exact hpb.lift_snd _ _ _

/-- Two invertible modules on `X_T` become isomorphic after pulling back along `g : T' ⟶ T`
exactly when their classes in `Pic(X_{T'})` agree. -/
private theorem nonempty_iso_modulePullback_iff {T T' : s.SchemesOver} (g : T' ⟶ T)
    (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) (hN : IsInvertibleModule (s.baseChange T) N) :
    Nonempty ((modulePullback B S hS (baseChangeMap s.f g)).obj L ≅
        (modulePullback B S hS (baseChangeMap s.f g)).obj N) ↔
      s.picardMap g (picardClass (s.baseChange T) L hL) =
        s.picardMap g (picardClass (s.baseChange T) N hN) := by
  rw [picardMap_eq, picardPullback_picardClass, picardPullback_picardClass,
    picardClass_eq_picardClass_iff]

/-- **The equalizer of the images of two Picard classes over an affine test scheme is fppf
locally covered by one quasi-compact scheme**, given the Isom input `hIsom`. Let `T` be an affine
test scheme, `v, w ∈ Pic(X_T)`, and `E` the equalizer of their images in `Pic_{X/B}(T)`. There is
a quasi-compact `W` with a morphism `w₀ : W ⟶ T` lying in `E` such that every point of every
`Q ⟶ T` lying in `E` is, after an arrow `V ⟶ Q` through it, the image of a point of `W`. -/
private theorem exists_compact_cover_picardEqualizer
    (hIsom : ∀ (T : s.SchemesOver), IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) →
      ∀ (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2),
        IsInvertibleModule (s.baseChange T) L → IsInvertibleModule (s.baseChange T) N →
        ∃ (W : BigFppfOver B S hS) (w : W ⟶ T.left),
          CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
          ∀ ⦃T' : s.SchemesOver⦄ (g : T' ⟶ T),
            (∃ l : T'.left ⟶ W, l ≫ w = g.left) ↔
              Nonempty ((modulePullback B S hS (baseChangeMap s.f g)).obj L ≅
                (modulePullback B S hS (baseChangeMap s.f g)).obj N))
    (T : s.SchemesOver) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (v w : s.picardAt T) :
    ∃ (W : BigFppfOver B S hS) (w₀ : W ⟶ T.left),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
      w₀ ∈ (s.picardEqualizer T (s.picardClassMap T v) (s.picardClassMap T w)).obj
        (Opposite.op W) ∧
      ∀ ⦃Q : BigFppfOver B S hS⦄ (k : Q ⟶ T.left),
        k ∈ (s.picardEqualizer T (s.picardClassMap T v) (s.picardClassMap T w)).obj
          (Opposite.op Q) →
        ∀ q : (BigFppfOver.toScheme B S hS).obj Q,
          ∃ (V : BigFppfOver B S hS) (f : V ⟶ Q) (l : V ⟶ W),
            l ≫ w₀ = f ≫ k ∧ q ∈ Set.range ((BigFppfOver.toScheme B S hS).map f).base := by
  obtain ⟨L, hL, rfl⟩ := exists_picardClass (s.baseChange T) v
  obtain ⟨N, hN, rfl⟩ := exists_picardClass (s.baseChange T) w
  obtain ⟨W, w₀, hWc, hW⟩ := hIsom T hT L N hL hN
  refine ⟨W, w₀, hWc, ?_, fun Q k hk q => ?_⟩
  · -- `W` maps into the equalizer: over `W` the two modules are isomorphic
    let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T w₀
    refine (s.mem_picardEqualizer_iff _ _ m).2 ?_
    rw [← s.picardClassMap_picardMap, ← s.picardClassMap_picardMap]
    exact congrArg _ ((s.nonempty_iso_modulePullback_iff m L N hL hN).1
      ((hW m).1 ⟨𝟙 _, Category.id_comp _⟩))
  · -- a point of the equalizer: the two modules are isomorphic fppf locally around it
    let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T k
    have hR := (s.mem_picardEqualizer_picardClassMap_iff T _ _ k).1 hk
    rw [CostructuredArrow.mem_restrictedTopology_proj_iff] at hR
    obtain ⟨c, r, hr, -, -, hq⟩ := BigFppfOver.exists_mem_of_mem_topology B S hS hR q
    obtain ⟨Z, n, h, hn, hfac⟩ := hr
    change s.picardMap n (s.picardMap m _) = s.picardMap n (s.picardMap m _) at hn
    rw [← s.picardMap_comp, ← s.picardMap_comp] at hn
    obtain ⟨l, hl⟩ := (hW (n ≫ m)).2 ((s.nonempty_iso_modulePullback_iff (n ≫ m) L N hL hN).2 hn)
    refine ⟨c, r, h ≫ l, ?_, hq⟩
    rw [Category.assoc, hl, hfac, Category.assoc]
    rfl

/-- **A scheme representing the equalizer of two points of `Pic_{X/B}(T)` is quasi-compact over
`T`**, given the Isom input `hIsom`. Here `j : P ⟶ T` is a monomorphism of the site through which
exactly the morphisms of the equalizer factor. -/
private theorem quasiCompact_of_represents_picardEqualizer_of_isom
    (hIsom : ∀ (T : s.SchemesOver), IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) →
      ∀ (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2),
        IsInvertibleModule (s.baseChange T) L → IsInvertibleModule (s.baseChange T) N →
        ∃ (W : BigFppfOver B S hS) (w : W ⟶ T.left),
          CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
          ∀ ⦃T' : s.SchemesOver⦄ (g : T' ⟶ T),
            (∃ l : T'.left ⟶ W, l ≫ w = g.left) ↔
              Nonempty ((modulePullback B S hS (baseChangeMap s.f g)).obj L ≅
                (modulePullback B S hS (baseChangeMap s.f g)).obj N))
    (T : s.SchemesOver) (x y : s.picardFunctor.obj (Opposite.op T))
    {P : BigFppfOver B S hS} (j : P ⟶ T.left) [Mono j]
    (hj : ∀ ⦃W : BigFppfOver B S hS⦄ (k : W ⟶ T.left),
      k ∈ (s.picardEqualizer T x y).obj (Opposite.op W) ↔ ∃ l : W ⟶ P, l ≫ j = k) :
    QuasiCompact ((BigFppfOver.toScheme B S hS).map j) := by
  classical
  let E := s.picardEqualizer T x y
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro Uo hUo
  obtain ⟨V, u, -, hurange, hVaff⟩ :=
    BigFppfOver.exists_affineOpen_restrict B S hS T.left ⟨Uo, hUo⟩
  -- the covering sieve along which `x` and `y` come from invertible modules
  let R : Sieve T := Presheaf.imageSieve s.toPicardFunctor x ⊓
    Presheaf.imageSieve s.toPicardFunctor y
  have hR : R ∈ s.fppfTopology T := s.fppfTopology.intersection_covering
    (Presheaf.imageSieve_mem s.fppfTopology s.toPicardFunctor x)
    (Presheaf.imageSieve_mem s.fppfTopology s.toPicardFunctor y)
  rw [CostructuredArrow.mem_restrictedTopology_proj_iff] at hR
  obtain ⟨I, hI, Vi, vi, hViaff, hViR, hVicov⟩ :=
    Stack.exists_finite_affine_family_of_mem_topology B S hS hVaff
      ((BigFppfOver.topology B S hS).pullback_stable u hR)
  have key : ∀ i, ∃ (Wi : BigFppfOver B S hS) (li : Wi ⟶ P),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj Wi) ∧
      Set.range ((BigFppfOver.toScheme B S hS).map li) ⊆
        (BigFppfOver.toScheme B S hS).map j ⁻¹ᵁ Uo ∧
      ∀ e : (BigFppfOver.toScheme B S hS).obj P,
        (BigFppfOver.toScheme B S hS).map j e ∈
            Set.range ((BigFppfOver.toScheme B S hS).map (vi i ≫ u)) →
          e ∈ Set.range ((BigFppfOver.toScheme B S hS).map li) := by
    intro i
    let g : Vi i ⟶ T.left := vi i ≫ u
    let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ :=
      (CostructuredArrow.mem_functorPushforward_proj_iff _ _ R m).1 (hViR i)
    obtain ⟨Wi, wi, hWc, hwi, hsurj⟩ :=
      s.exists_compact_cover_picardEqualizer hIsom _ (hViaff i) v w
    have hEi : ∀ ⦃Q : BigFppfOver B S hS⦄ (k : Q ⟶ Vi i),
        k ∈ (s.picardEqualizer _ (s.picardClassMap _ v) (s.picardClassMap _ w)).obj
          (Opposite.op Q) ↔ k ≫ g ∈ E.obj (Opposite.op Q) := by
      intro Q k
      have h := s.picardEqualizer_preimage T x y g
      have hv' : s.picardClassMap _ v = s.picardFunctor.map m.op x := hv
      have hw' : s.picardClassMap _ w = s.picardFunctor.map m.op y := hw
      rw [hv', hw', ← h]
      rfl
    obtain ⟨li, hli⟩ := (hj (wi ≫ g)).1 ((hEi wi).1 hwi)
    refine ⟨Wi, li, hWc, ?_, fun e he => ?_⟩
    · rintro _ ⟨w', rfl⟩
      show ((BigFppfOver.toScheme B S hS).map li ≫ (BigFppfOver.toScheme B S hS).map j) w' ∈
        (Uo : Set _)
      rw [← Functor.map_comp, hli, Functor.map_comp, Functor.map_comp, ← hurange]
      exact ⟨_, rfl⟩
    · obtain ⟨t, ht⟩ := he
      have hpbS := (IsPullback.of_hasPullback j g).map (BigFppfOver.toScheme B S hS)
      obtain ⟨qpt, hq₁, -⟩ := _root_.AlgebraicGeometry.exists_point_of_isPullback hpbS e t ht.symm
      have hk : pullback.snd j g ∈ (s.picardEqualizer _ (s.picardClassMap _ v)
          (s.picardClassMap _ w)).obj (Opposite.op (pullback j g)) :=
        (hEi _).2 ((hj _).2 ⟨pullback.fst j g, pullback.condition⟩)
      obtain ⟨V', f, l, hl, hqf⟩ := hsurj _ hk qpt
      have hll : l ≫ li = f ≫ pullback.fst j g := by
        rw [← cancel_mono j, Category.assoc, hli, ← Category.assoc, hl, Category.assoc,
          Category.assoc, pullback.condition]
      obtain ⟨q', rfl⟩ := hqf
      refine ⟨(BigFppfOver.toScheme B S hS).map l q', ?_⟩
      rw [← hq₁, ← Scheme.Hom.comp_apply, ← Functor.map_comp, hll, Functor.map_comp,
        Scheme.Hom.comp_apply]
  choose Wi li hWc hrange hcov using key
  have hset : ((BigFppfOver.toScheme B S hS).map j ⁻¹ᵁ Uo : Set _) =
      ⋃ i, Set.range ((BigFppfOver.toScheme B S hS).map (li i)) := by
    refine Set.Subset.antisymm (fun e he => ?_) (Set.iUnion_subset hrange)
    have he' : (BigFppfOver.toScheme B S hS).map j e ∈ (Uo : Set _) := he
    rw [← hurange] at he'
    obtain ⟨t, ht⟩ := he'
    obtain ⟨i, t', ht'⟩ := hVicov t
    refine Set.mem_iUnion.2 ⟨i, hcov i e ⟨t', ?_⟩⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, ht', ht]
  rw [hset]
  have := hI
  exact isCompact_iUnion fun i =>
    have := hWc i
    isCompact_range ((BigFppfOver.toScheme B S hS).map (li i)).continuous

/-- **The diagonal of an algebraic model of `Pic_{X/B}` over `B` is quasi-compact**, given the
Isom input `hIsom`. Here `q : F ⟶ B` is a morphism from an algebraic space whose fibres are
identified (`e`, naturally in the test scheme by `he`) with `Pic_{X/B}`. -/
private theorem isQuasiCompact_diagonal_of_represents_of_isom
    (hIsom : ∀ (T : s.SchemesOver), IsAffine ((BigFppfOver.toScheme B S hS).obj T.left) →
      ∀ (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2),
        IsInvertibleModule (s.baseChange T) L → IsInvertibleModule (s.baseChange T) N →
        ∃ (W : BigFppfOver B S hS) (w : W ⟶ T.left),
          CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
          ∀ ⦃T' : s.SchemesOver⦄ (g : T' ⟶ T),
            (∃ l : T'.left ⟶ W, l ≫ w = g.left) ↔
              Nonempty ((modulePullback B S hS (baseChangeMap s.f g)).obj L ≅
                (modulePullback B S hS (baseChangeMap s.f g)).obj N))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) (q : F ⟶ s.base.1)
    (e : ∀ T : s.SchemesOver, s.picardFunctor.obj (Opposite.op T) ≃
      {x : F.obj (Opposite.op T.left) //
        q.app (Opposite.op T.left) x =
          yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom)})
    (he : ∀ (T U : s.SchemesOver) (g : T ⟶ U) (x : s.picardFunctor.obj (Opposite.op U)),
      (e T (s.picardFunctor.map g.op x)).val = F.map g.left.op (e U x).val) :
    IsQuasiCompact B S hS (pullback.diagonal q) := by
  refine isQuasiCompact_of_presheaf_quasiCompact B S hS
    ⟨relativelyRepresentable_pullbackDiagonal B S hS q hF, ?_⟩
  intro a b h fst snd hpb
  -- the test scheme over `a` and the two points of `Pic_{X/B}` named by `h`
  let x₀ : F.obj (Opposite.op a) := yonedaEquiv (h ≫ pullback.fst q q)
  let y₀ : F.obj (Opposite.op a) := yonedaEquiv (h ≫ pullback.snd q q)
  have hq : q.app _ x₀ = q.app _ y₀ := by
    simp only [x₀, y₀, ← yonedaEquiv_comp, Category.assoc, pullback.condition]
  let hb : (schemeSpaceFunctor B S hS).obj a ⟶ s.base :=
    ObjectProperty.homMk (yonedaEquiv.symm (q.app _ x₀))
  let T : s.SchemesOver := CostructuredArrow.mk hb
  have hT : yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom) = q.app _ x₀ :=
    yonedaEquiv.apply_symm_apply _
  let x := (e T).symm ⟨x₀, hT.symm⟩
  let y := (e T).symm ⟨y₀, hq.symm.trans hT.symm⟩
  have hEq : diagonalEqualizer q h = s.picardEqualizer T x y :=
    s.diagonalEqualizer_eq_picardEqualizer F q e he T h x y (by simp [x, x₀]) (by simp [y, y₀])
  -- `snd` represents the equalizer
  have hfac : ∀ ⦃W : BigFppfOver B S hS⦄ (k : W ⟶ a),
      k ∈ (diagonalEqualizer q h).obj (Opposite.op W) ↔ ∃ l : W ⟶ b, l ≫ snd = k := by
    intro W k
    rw [mem_diagonalEqualizer_iff]
    constructor
    · intro hk
      have hd : (yoneda.map k ≫ h ≫ pullback.fst q q) ≫ pullback.diagonal q =
          yoneda.map k ≫ h := by
        apply pullback.hom_ext
        · simp
        · simp [hk]
      exact exists_comp_eq_of_isPullback_yoneda hpb _ k hd
    · rintro ⟨l, rfl⟩
      have hw := hpb.w
      simp only [Functor.map_comp, Category.assoc, ← reassoc_of% hw, pullback.diagonal_fst,
        pullback.diagonal_snd]
  have hmono : Mono snd := by
    refine ⟨fun l₁ l₂ hl => yoneda.map_injective ?_⟩
    have h2 : yoneda.map l₁ ≫ yoneda.map snd = yoneda.map l₂ ≫ yoneda.map snd := by
      rw [← Functor.map_comp, ← Functor.map_comp, hl]
    refine hpb.hom_ext ?_ h2
    rw [← cancel_mono (pullback.diagonal q), Category.assoc, Category.assoc, hpb.w,
      reassoc_of% h2]
  rw [hEq] at hfac
  exact s.quasiCompact_of_represents_picardEqualizer_of_isom hIsom T x y snd hfac

/-! ### The Isom input from the relative Isom functor -/

/-- **The relative Hom situation of two invertible modules on `X_T`**, over the test scheme `T`
read as an algebraic space: the projection `X_T ⟶ T` with the two modules, which are
quasi-coherent because they are invertible. Its relative Isom functor (Stacks 08K7) is
`Isom(L, N)`, a functor on the schemes over `T`. -/
abbrev isomHomSituation (T : s.SchemesOver)
    (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) (hN : IsInvertibleModule (s.baseChange T) N) :
    HomSituation B S hS where
  X := s.baseChange T
  base := (schemeSpaceFunctor B S hS).obj T.left
  f := baseChangeInclusion s.f T
  F := L
  G := N
  quasicoherent_F := isQuasicoherentOnSite_of_isInvertibleModule _ L hL
  quasicoherent_G := isQuasicoherentOnSite_of_isInvertibleModule _ N hN

/-- Inverse image along an isomorphism of algebraic spaces reflects the existence of an
isomorphism of modules. -/
private theorem nonempty_iso_of_modulePullback_iso {A A' : AlgebraicSpaces B S hS} (φ : A ≅ A')
    {M N : Modules.{u, u} B S hS A'.1 A'.2}
    (e : (modulePullback B S hS φ.hom).obj M ≅ (modulePullback B S hS φ.hom).obj N) :
    Nonempty (M ≅ N) := by
  let hc := modulePushforwardCoherence B S hS
  let t := modulePullbackTriangle B S hS φ.inv_hom_id
  exact ⟨(hc.modulePullbackIdIso A').symm.app M ≪≫ t.app M ≪≫
    (modulePullback B S hS φ.inv).mapIso e ≪≫ (t.app N).symm ≪≫ (hc.modulePullbackIdIso A').app N⟩

/-- **The comparison of the two base changes.** For a morphism of test schemes `g : T' ⟶ T` the
base change of `X_T ⟶ T` along `T' ⟶ T` is identified with `X_{T'}`, compatibly with the maps to
`X_T`, by pasting the two cartesian squares. -/
private theorem exists_iso_baseChange_isomHomSituation {T T' : s.SchemesOver} (g : T' ⟶ T)
    (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) (hN : IsInvertibleModule (s.baseChange T) N) :
    ∃ φ : (s.isomHomSituation T L N hL hN).baseChange
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left)) ≅ s.baseChange T',
      φ.hom ≫ baseChangeMap s.f g = (s.isomHomSituation T L N hL hN).projection
        (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left)) := by
  let hs := s.isomHomSituation T L N hL hN
  let T'' : hs.SchemesOver := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left)
  have sq1 : IsPullback (baseChangeProjection s.f T) (baseChangeInclusion s.f T) s.f T.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS s.f T.hom
  have sq2 : IsPullback (hs.projection T'') (baseChangeInclusion hs.f T'')
      (baseChangeInclusion s.f T) T''.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS hs.f T''.hom
  have sq3 : IsPullback (baseChangeProjection s.f T') (baseChangeInclusion s.f T') s.f T'.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS s.f T'.hom
  have hw : T''.hom ≫ T.hom = T'.hom := CostructuredArrow.w g
  have sq : IsPullback (hs.projection T'' ≫ baseChangeProjection s.f T)
      (baseChangeInclusion hs.f T'') s.f T'.hom := by
    rw [← hw]
    exact sq2.paste_horiz sq1
  let φ := sq.isoIsPullback _ _ sq3
  refine ⟨φ, baseChange_hom_ext s.f ?_ ?_⟩
  · rw [Category.assoc, baseChangeMap_comp_projection]
    exact sq.isoIsPullback_hom_fst _ _ sq3
  · rw [Category.assoc, baseChangeMap_comp_inclusion, ← Category.assoc,
      sq.isoIsPullback_hom_snd _ _ sq3]
    exact sq2.w.symm

/-- **An isomorphism of the pullbacks of `L` and `N` along a morphism of test schemes is a point
of `Isom(L, N)`.** For `g : T' ⟶ T`, the modules pulled back to `X_{T'}` are isomorphic exactly
when the relative Isom functor of `L` and `N` has a section over `T'`, read as a scheme over `T`
through `g`. -/
private theorem nonempty_isomFunctor_iff {T T' : s.SchemesOver} (g : T' ⟶ T)
    (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) (hN : IsInvertibleModule (s.baseChange T) N) :
    Nonempty ((s.isomHomSituation T L N hL hN).isomFunctor.obj
        (Opposite.op (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left)))) ↔
      Nonempty ((modulePullback B S hS (baseChangeMap s.f g)).obj L ≅
        (modulePullback B S hS (baseChangeMap s.f g)).obj N) := by
  let hs := s.isomHomSituation T L N hL hN
  let T'' : hs.SchemesOver := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left)
  obtain ⟨φ, hφ⟩ := s.exists_iso_baseChange_isomHomSituation g L N hL hN
  let t := modulePullbackTriangle B S hS hφ
  have key : Nonempty (hs.isomFunctor.obj (Opposite.op T'')) ↔
      Nonempty ((modulePullback B S hS (hs.projection T'')).obj L ≅
        (modulePullback B S hS (hs.projection T'')).obj N) := by
    rw [hs.isomFunctor_obj T'']
    constructor
    · rintro ⟨α, hα⟩
      exact ⟨@asIso _ _ _ _ (hs.toModuleHom α) hα⟩
    · rintro ⟨e⟩
      exact ⟨⟨e.hom, (hs.isIsomAt_iff (T := T'') e.hom).2 (inferInstanceAs (IsIso e.hom))⟩⟩
  refine key.trans ⟨fun ⟨e⟩ => ?_, fun ⟨e⟩ => ?_⟩
  · exact nonempty_iso_of_modulePullback_iso φ ((t.app L).symm ≪≫ e ≪≫ t.app N)
  · exact ⟨t.app L ≪≫ (modulePullback B S hS φ.hom).mapIso e ≪≫ (t.app N).symm⟩

/-- **The Isom input from the relative Isom functor.** If `Isom(L, N)` is an algebraic space
affine over an affine test scheme `T`, it is represented by an affine scheme `W ⟶ T`, through
which a morphism of test schemes `g : T' ⟶ T` factors exactly when `g^*L ≅ g^*N`. -/
private theorem exists_compact_isom_of_isAffineAlgebraicSpaceOver (T : s.SchemesOver)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
    (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) (hN : IsInvertibleModule (s.baseChange T) N)
    (h : IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T.left)
      (s.isomHomSituation T L N hL hN).isomFunctor) :
    ∃ (W : BigFppfOver B S hS) (w : W ⟶ T.left),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
      ∀ ⦃T' : s.SchemesOver⦄ (g : T' ⟶ T),
        (∃ l : T'.left ⟶ W, l ≫ w = g.left) ↔
          Nonempty ((modulePullback B S hS (baseChangeMap s.f g)).obj L ≅
            (modulePullback B S hS (baseChangeMap s.f g)).obj N) := by
  obtain ⟨H, p, hp, ⟨c⟩⟩ := h
  obtain ⟨W, pW, qW, hpb⟩ := hp ⟨T.left, hT⟩ (𝟙 _)
  let W' : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj W
  have hWc : CompactSpace ((BigFppfOver.toScheme B S hS).obj W') :=
    @Scheme.compactSpace_of_isAffine _ W.property
  refine ⟨W', qW, hWc, fun T' g => ?_⟩
  let T'' : _root_.AlgebraicGeometry.Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T.left) :=
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left)
  have htp : testPoint T'' = yonedaEquiv (yoneda.map g.left) := rfl
  refine Iff.trans ?_ (s.nonempty_isomFunctor_iff g L N hL hN)
  constructor
  · rintro ⟨l, hl⟩
    let x : H.1.obj (Opposite.op T'.left) := yonedaEquiv (yoneda.map l ≫ pW)
    have hx : p.hom.app _ x = testPoint T'' := by
      have hw : pW ≫ p.hom = yoneda.map qW := hpb.w.trans (Category.comp_id _)
      have h1 : (yoneda.map l ≫ pW) ≫ p.hom = yoneda.map g.left := by
        rw [Category.assoc, hw]
        exact (yoneda.map_comp l qW).symm.trans (congrArg yoneda.map hl)
      exact (yonedaEquiv_comp _ _).symm.trans ((congrArg yonedaEquiv h1).trans htp.symm)
    exact ⟨c.hom.app (Opposite.op T'') (ULift.up ⟨x, hx⟩)⟩
  · rintro ⟨ξ⟩
    let x := (c.inv.app (Opposite.op T'') ξ).down
    have hx : yonedaEquiv.symm x.1 ≫ p.hom = yoneda.map g.left ≫ 𝟙 _ := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, x.2, Category.comp_id, htp]
      rfl
    exact exists_comp_eq_of_isPullback_yoneda hpb _ g.left hx

variable {s} {H : AlgebraicSpaces B S hS} {p : H ⟶ s.base}

/-- **An algebraic space representing `Pic_{X/B}` is quasi-separated over `B`, given that
`Isom(L, N)` is affine over the base** (the first half of Stacks 0DNI, from the
quasi-compactness half of Stacks 0DMF). Let `p : H ⟶ B` be an algebraic space over `B` whose
functor of points over `B` is identified (`c`) with `Pic_{X/B}`. Suppose that for any two
invertible modules `L`, `N` on `X_T` over an affine test scheme `T`, the relative Isom functor
`Isom(L, N)` of `X_T ⟶ T` (Stacks 08K7) is an algebraic space affine over `T` (`hIsom`; this is
Stacks 08K9 for `X_T ⟶ T`, which applies when `f` is flat, proper and of finite presentation,
and it is what Stacks 0DMA reads at the point `(L, N)`). Then `p` is quasi-separated.

The proof is that of Stacks 0DMF: the diagonal of `H`, read at a point of `H ×_B H` over `T`, is
the equalizer of two points of `Pic_{X/B}(T)`; fppf locally on `T` these come from invertible
modules (Stacks 0DME), and there the equalizer is covered by the affine scheme representing
their `Isom`. Not registered: `hIsom` is not yet discharged. -/
theorem isQuasiSeparated_of_represents_of_isAffineAlgebraicSpaceOver_isomFunctor
    (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ s.picardFunctor)
    (hIsom : ∀ (T : s.SchemesOver) (_hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left))
      (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
      (hL : IsInvertibleModule (s.baseChange T) L) (hN : IsInvertibleModule (s.baseChange T) N),
      IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T.left)
        (s.isomHomSituation T L N hL hN).isomFunctor) :
    IsQuasiSeparated B S hS p.hom := by
  let e : ∀ T : s.SchemesOver, s.picardFunctor.obj (Opposite.op T) ≃
      {x : H.1.obj (Opposite.op T.left) //
        p.hom.app (Opposite.op T.left) x =
          yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom)} := fun T =>
    { toFun := fun ξ => (c.inv.app (Opposite.op T) ξ).down
      invFun := fun x => c.hom.app (Opposite.op T) (ULift.up x)
      left_inv := fun ξ => (c.app (Opposite.op T)).inv_hom_id_apply ξ
      right_inv := fun x => by
        have h := (c.app (Opposite.op T)).hom_inv_id_apply
          (show (spacePointsOver p ⋙ uliftFunctor.{u + 1, u}).obj (Opposite.op T) from
            ULift.up x)
        exact congrArg ULift.down h }
  have he : ∀ (T U : s.SchemesOver) (g : T ⟶ U) (ξ : s.picardFunctor.obj (Opposite.op U)),
      (e T (s.picardFunctor.map g.op ξ)).val = H.1.map g.left.op (e U ξ).val := by
    intro T U g ξ
    show (c.inv.app (Opposite.op T) (s.picardFunctor.map g.op ξ)).down.1 = _
    rw [NatTrans.naturality_apply]
    rfl
  exact s.isQuasiCompact_diagonal_of_represents_of_isom
    (fun T hT L N hL hN => s.exists_compact_isom_of_isAffineAlgebraicSpaceOver T hT L N hL hN
      (hIsom T hT L N hL hN)) H.1 H.2 p.hom e he

end AlgebraicGeometry.Space.PicardSituation

end
