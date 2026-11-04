module

public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Etale.FilteredColimitStage
public import StacksFrontier.RingTheory.Smoothing.IndSmoothColimitPresentation

/-!
# Descending an étale algebra over a base change of an ind-smooth algebra to a smooth stage

Let `R → Λ` be ind-smooth (`Stacks.Smoothing.IndSmooth`, the conclusion of Popescu's theorem
`07GC`), let `C` be an `R`-algebra of finite presentation with an `R`-algebra map to `Λ`, and let
`B` be a `C`-algebra. Then `B ⊗[C] Λ` is the filtered colimit of the `B ⊗[C] R'` for `R'` a
`C`-algebra smooth over `R`
(`Stacks.Smoothing.exists_colimitPresentation_tensorProduct_of_indSmooth`), and an étale algebra
over a filtered colimit comes from a stage (item (9) of Stacks `00U2`,
`Algebra.Etale.exists_etale_stage_of_isColimit`). This file composes the two: **an étale algebra
over `B ⊗[C] Λ` is the base change of an étale algebra over `B ⊗[C] R'` for a single `R'` smooth
over `R`.**

This is the first half of the step of the proof of Stacks `0CAW` reading "Note that
`R^\wedge = \mathop{\mathrm{colim}} R'` ... Thus we may assume that `B'` is the base change of an
étale `B ⊗_C R'`-algebra": there `Λ = R^\wedge`, `C` and `B` are the chart rings of `T` and `Y`,
and `B'` is the étale algebra over `B ⊗_{C, σ} R^\wedge` that
`StacksDraft.ArtinApproximation.exists_etale_tensorProduct_chart` produces.

A second theorem carries the *map* of the same step along: if `A` is an `R`-algebra of finite
presentation and `A → B'` is an `R`-algebra map, then `A → B'` descends to the stage as well, so
that the whole of "we may replace `C` by `R'` and `B` by `B''`" is available and not only its
algebra half.

## Main results

* `Stacks.Smoothing.exists_smooth_stage_etale_tensorProduct_of_indSmooth`: the statement above.
* `Stacks.Smoothing.exists_smooth_stage_etale_map_tensorProduct_of_indSmooth`: the same, with an
  `R`-algebra map `A → B'` out of an `R`-algebra `A` of finite presentation descended to a map
  `A → B''` compatibly.

Neither carries a prime or a residue field datum, and clause (4) of Tag `0CAW` needs one: a prime
of `B''` over `𝔭_{B ⊗[C] R'}` with trivial residue extension. It is not part of these statements
because it is not part of the descent — it is recovered afterwards, from residual triviality of
`R' → Λ` at the prime of `Λ`, by
`Ideal.exists_isPrime_comap_eq_and_residueField_map_bijective_of_descent_algEquiv`
(`StacksFrontier/RingTheory/Flat/ElementaryEtaleStageDescent.lean`). In particular **the stage these
theorems return needs no enlargement** on clause (4)'s account.

## Implementation notes

The colimit presentation used is the one over `C`,
`Stacks.Smoothing.exists_colimitPresentation_smooth_of_indSmooth`, tensored here rather than the
already-tensored
`Stacks.Smoothing.exists_colimitPresentation_tensorProduct_of_indSmooth`: the latter pins down
only the *diagram* of the presentation, while the conclusion below has to name the map
`R' → Λ` through which the stage sits over `Λ`, and that map is a *cocone leg*. Tensoring here
keeps both halves of the presentation available, and the cocone leg of the tensored presentation
is then literally `1 ⊗ ρ` for `ρ : R' →ₐ[C] Λ` the leg of the presentation over `C`, since
`CommRingCat.tensorProd` acts on morphisms by `Algebra.TensorProduct.map (AlgHom.id B B)`.

The algebra structure making `B ⊗[C] Λ` an algebra over the stage `B ⊗[C] R'` is therefore
supplied in the statement as `1 ⊗ ρ`, not existentially: without it the conclusion would say
that `B'` is a base change of an étale algebra along *some* map, which does not place `B'` over
the smooth stage at all.

*Where the `IndSmooth R Λ` hypothesis comes from at Tag `0CAW`'s own data.* There `Λ = R^∧` is
the completion of the *localization* of the chart ring `R` at the chosen prime, and `0CAW`
assumes only that `R_𝔭 = 𝒪_{S, s}` is a G-ring, not that `R` is. So
`Stacks.Smoothing.indSmooth_adicCompletion_of_isGRing`, which is about `A → A^∧` at one and the
same ring, does not apply; the form that does is
`Stacks.Smoothing.indSmooth_adicCompletion_maximalIdeal_of_isLocalization`.

The stage's smoothness over `R` is stated as `RingHom.Smooth` of the composite
`R → C → R'`, as in `Stacks.Smoothing.exists_colimitPresentation_smooth_of_indSmooth`, rather
than as `Algebra.Smooth R R'`, which would need an `Algebra R R'` instance that the diagram of
the presentation does not provide.

*How the map is descended.* Descending `A → B'` is not a reindexing of the descent of `B'`: it
needs `B'` itself exhibited as a filtered colimit. Once a stage `j` and an étale
`f' : B ⊗[C] R'_j → T'` with `B' = (B ⊗[C] Λ) ⊗_{B ⊗[C] R'_j} T'` are given — by
`exists_isPushout_etale`, the pushout-square form of item (9) of `00U2` — the cobase changes
`T' ⊗_{B ⊗[C] R'_j} (B ⊗[C] R'_k)` over the tail `Under j` form a filtered diagram whose colimit
is `B'`, because `CategoryTheory.Under.pushout` is a left adjoint and `Under.forget j` is final.
`A` is finitely presentable over `R`, so `A → B'` factors through one of those stages, and that
stage is again étale over `B ⊗[C] R'_k` and still has `B'` as its base change, by cancelling the
pushout square of the tail step out of the pushout square at `j`
(`CategoryTheory.IsPushout.of_left`).

Mathlib's `CategoryTheory.MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads` and
this repository's `CommRingCat.exists_factorization_of_ind_pushout` do *not* give this. The
former concludes that `MorphismProperty.ind CommRingCat.etale` is stable under composition, which
is a statement about `B → B'` and says nothing about a map into `B'` from a third ring; the
latter factors a map whose *source* is an algebra over the ring being base changed and whose
*target* is literally a base change `A ⊗_R Λ`, whereas here the source `A` is an algebra over `R`
and the target `B'` is étale over the base change rather than being one.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW), whose proof's descent
  step this is
* [Stacks Project, Tag 00U2](https://stacks.math.columbia.edu/tag/00U2), item (9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.Smoothing

/-- The structure maps `X → F k` of a diagram `F` of objects under `X`, as a natural
transformation. -/
private def underStructureHom {J : Type u} [SmallCategory J] {X : CommRingCat.{u}}
    (F : J ⥤ Under X) : (Functor.const J).obj X ⟶ F ⋙ Under.forget X where
  app k := (F.obj k).hom
  naturality _ _ a := (Category.id_comp _).trans (Under.w (F.map a)).symm

/-- **An étale map out of a filtered colimit, together with a compatible map into its target from a
finitely presentable algebra, descends to a stage as a pushout square.** Let `c` be a filtered
colimit of `D` in `CommRingCat`, `f : c.pt → X` étale, `s` a cocone of `D` under a constant ring
`R`, and `α : A → X` compatible with `s` along a finitely presentable `i : R → A`; then some stage
`D k` has an étale `ι : D k → T` whose cobase change along `c.ι k` is `f`, and `α` factors through
`T` by a map `v` compatible with `s` along `ι`. -/
private theorem exists_etale_isPushout_stage_of_isColimit {J : Type u} [SmallCategory J]
    [IsFiltered J] {D : J ⥤ CommRingCat.{u}} {c : Cocone D} (hc : IsColimit c) {X : CommRingCat.{u}}
    (f : c.pt ⟶ X) (hf : CommRingCat.etale.{u} f) {R A : CommRingCat.{u}}
    (s : (Functor.const J).obj R ⟶ D) (i : R ⟶ A) [IsFinitelyPresentable.{u} (Under.mk i)]
    (α : A ⟶ X) (hα : ∀ j, s.app j ≫ c.ι.app j ≫ f = i ≫ α) :
    ∃ (k : J) (T : CommRingCat.{u}) (ι : D.obj k ⟶ T) (g : T ⟶ X) (v : A ⟶ T),
      CommRingCat.etale.{u} ι ∧ IsPushout (c.ι.app k) ι f g ∧ i ≫ v = s.app k ≫ ι ∧
        v ≫ g = α := by
  obtain ⟨j, T', f', g, hsq, hf'⟩ := exists_isPushout_etale hc f hf
  -- spread the étale map `f'` over the tail `Under j`: `X` is the filtered colimit of the
  -- cobase changes `T' ⊗_{D j} D k` of `f'`.
  let Dpost : Under j ⥤ Under T' := Under.post D ⋙ Under.pushout f'
  let cpost : Cocone Dpost := (Under.pushout f').mapCocone (c.underPost j)
  have hcpost : IsColimit cpost := isColimitOfPreserves _ (hc.underPost j)
  let D' : Under j ⥤ CommRingCat.{u} := Dpost ⋙ Under.forget T'
  let c'₀ : Cocone D' := (Under.forget T').mapCocone cpost
  have hc'₀ : IsColimit c'₀ := isColimitOfPreserves _ hcpost
  let c' : Cocone D' := c'₀.extend hsq.isoPushout.inv
  have hc' : IsColimit c' :=
    hc'₀.ofIsoColimit (Cocone.ext hsq.isoPushout.symm (fun _ ↦ rfl))
  -- the structure maps over `T'` at the tail
  let sT : (Functor.const (Under j)).obj T' ⟶ D' := underStructureHom Dpost
  let s' : (Functor.const (Under j)).obj R ⟶ D' :=
    (Functor.const (Under j)).map (s.app j ≫ f') ≫ sT
  -- the two legs into a stage of the tail, and how each meets the colimit
  have hsT : ∀ k : Under j, sT.app k ≫ c'.ι.app k = g := fun k ↦
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ hsq.isoPushout.inv) (Under.w (cpost.ι.app k))).trans
        hsq.inr_isoPushout_inv)
  have hinl : ∀ k : Under j,
      pushout.inl ((Under.post D).obj k).hom f' ≫ c'.ι.app k = c.ι.app k.right ≫ f := fun k ↦
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ hsq.isoPushout.inv) (pushout.inl_desc _ _ _)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (c.ι.app k.right ≫ ·) hsq.inl_isoPushout_inv)))
  -- the two legs agree, so `s'` is also the composite through the stage's own base
  have hnat : ∀ k : Under j, s.app j ≫ D.map k.hom = s.app k.right := fun k ↦
    (s.naturality k.hom).symm.trans (Category.id_comp _)
  have hs'inl : ∀ k : Under j,
      s'.app k = s.app k.right ≫ pushout.inl ((Under.post D).obj k).hom f' := fun k ↦
    (Category.assoc _ _ _).trans
      ((congrArg (s.app j ≫ ·)
          (pushout.condition (f := ((Under.post D).obj k).hom) (g := f')).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ pushout.inl ((Under.post D).obj k).hom f') (hnat k))))
  have hcompat : ∀ k : Under j, s'.app k ≫ c'.ι.app k = i ≫ α := fun k ↦
    ((Category.assoc (s.app j ≫ f') (sT.app k) (c'.ι.app k)).trans
      (congrArg ((s.app j ≫ f') ≫ ·) (hsT k))).trans
      (((Category.assoc _ _ _).trans (congrArg (s.app j ≫ ·) hsq.w.symm)).trans (hα j))
  obtain ⟨k, v, hv₁, hv₂⟩ := IsFinitelyPresentable.exists_hom_of_isColimit_under hc' i s' α hcompat
  have hs : IsPushout (D.map k.hom ≫ c.ι.app k.right) f' f
      (pushout.inr ((Under.post D).obj k).hom f' ≫ c'.ι.app k) := by
    rwa [c.w k.hom,
      show pushout.inr ((Under.post D).obj k).hom f' ≫ c'.ι.app k = g from hsT k]
  exact ⟨k.right, D'.obj k, pushout.inl ((Under.post D).obj k).hom f', c'.ι.app k, v,
    CommRingCat.etale.pushout_inl (D.map k.hom) f' hf',
    IsPushout.of_left hs (hinl k).symm (IsPushout.of_hasPushout _ _), hv₁.trans (hs'inl k), hv₂⟩

/-- **An étale algebra over `B ⊗[C] Λ` together with a map into it from a finitely presented
`R`-algebra both descend to a smooth stage.** Let `Λ` be a filtered colimit of smooth
`R`-algebras, let `C` be an `R`-algebra of finite presentation with an `R`-algebra map
`σ : C → Λ`, let `B` be a `C`-algebra, let `A` be an `R`-algebra of finite presentation, let `B'`
be an étale `B ⊗[C] Λ`-algebra and let `α : A → B'` be a ring homomorphism compatible with the
structure maps of `A` and `B'` over `R`. Then there are a `C`-algebra `R'` whose structure map
`R → C → R'` is smooth, a `C`-algebra map `ρ : R' → Λ`, an étale `B ⊗[C] R'`-algebra `B''`, an
isomorphism `e` of `B ⊗[C] Λ`-algebras exhibiting `B'` as the base change of `B''` along
`1 ⊗ ρ : B ⊗[C] R' → B ⊗[C] Λ`, and a ring homomorphism `β : A → B''` compatible with the
structure maps over `R`, such that `α` is `β` followed by `B'' → B'`, i.e.
`e (α a) = 1 ⊗ β a` for every `a`.

In the notation of the proof of Stacks `0CAW` this is the full step "Thus we may assume that `B'`
is the base change of an étale `B ⊗_C R'`-algebra ... we may replace `C` by `R'` and `B` by
`B''`", with `Λ = R^\wedge`, `A` the chart ring of `X` and `α` the map `A → B'` that the previous
step produces. The algebra half alone is
`Stacks.Smoothing.exists_smooth_stage_etale_tensorProduct_of_indSmooth`. -/
theorem exists_smooth_stage_etale_map_tensorProduct_of_indSmooth
    (R C Λ : Type u) [CommRing R] [CommRing C] [CommRing Λ] [Algebra R C] [Algebra R Λ]
    [Algebra.FinitePresentation R C] (σ : C →ₐ[R] Λ)
    (B : Type u) [CommRing B] [Algebra C B]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (B' : Type u) [CommRing B'] (h : IndSmooth R Λ) :
    letI : Algebra C Λ := σ.toRingHom.toAlgebra
    ∀ [Algebra (B ⊗[C] Λ) B'], Algebra.Etale (B ⊗[C] Λ) B' →
      ∀ α : A →+* B',
        α.comp (algebraMap R A) =
            ((algebraMap (B ⊗[C] Λ) B').comp
              ((algebraMap B (B ⊗[C] Λ)).comp (algebraMap C B))).comp (algebraMap R C) →
      ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra C R'),
        ((algebraMap C R').comp (algebraMap R C)).Smooth ∧
          ∃ (ρ : R' →ₐ[C] Λ) (B'' : Type u) (_ : CommRing B'')
            (_ : Algebra (B ⊗[C] R') B''), Algebra.Etale (B ⊗[C] R') B'' ∧
            (letI : Algebra (B ⊗[C] R') (B ⊗[C] Λ) :=
                (Algebra.TensorProduct.map (AlgHom.id B B) ρ).toRingHom.toAlgebra;
              ∃ (e : B' ≃ₐ[B ⊗[C] Λ] (B ⊗[C] Λ) ⊗[B ⊗[C] R'] B'') (β : A →+* B''),
                β.comp (algebraMap R A) =
                    ((algebraMap (B ⊗[C] R') B'').comp
                      ((algebraMap B (B ⊗[C] R')).comp (algebraMap C B))).comp
                      (algebraMap R C) ∧
                  ∀ a : A, e (α a) = 1 ⊗ₜ[B ⊗[C] R'] β a) := by
  let : Algebra C Λ := σ.toRingHom.toAlgebra
  have : IsScalarTower R C Λ := .of_algebraMap_eq fun r ↦ (σ.commutes r).symm
  intro instB' hetale α hα
  obtain ⟨J, _, _, pres₀, hsmooth⟩ := exists_colimitPresentation_smooth_of_indSmooth R C Λ h
  let presU : ColimitPresentation J (CommRingCat.mkUnder (CommRingCat.of B) (B ⊗[C] Λ)) :=
    pres₀.tensorProd (S := CommRingCat.of B)
  let pres : ColimitPresentation J (CommRingCat.of (B ⊗[C] Λ)) :=
    presU.map (Under.forget (CommRingCat.of B))
  let D : J ⥤ CommRingCat.{u} := pres.diag
  let c : Cocone D := Cocone.mk _ pres.ι
  let fB : c.pt ⟶ CommRingCat.of B' := CommRingCat.ofHom (algebraMap (B ⊗[C] Λ) B')
  -- the structure maps of the diagram over `B`, hence over `R`
  let iRB : CommRingCat.of R ⟶ CommRingCat.of B :=
    CommRingCat.ofHom ((algebraMap C B).comp (algebraMap R C))
  let sB : (Functor.const J).obj (CommRingCat.of B) ⟶ D := underStructureHom presU.diag
  -- `A` is of finite presentation over `R`, so `A → B'` factors through a stage of the tail
  have : IsFinitelyPresentable.{u} (Under.mk (CommRingCat.ofHom (algebraMap R A))) :=
    CommRingCat.isFinitelyPresentable_hom _ (RingHom.finitePresentation_algebraMap.mpr ‹_›)
  obtain ⟨k, T, ιP, g, v, hιP, hsq, hv₁, hv₂⟩ := exists_etale_isPushout_stage_of_isColimit
    (pres.isColimit : IsColimit c) fB (RingHom.etale_algebraMap.mpr hetale)
    ((Functor.const J).map iRB ≫ sB) (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom α) fun j ↦ by
      -- the structure map of `B ⊗[C] Λ` over `B` is the leg of the tensored presentation
      refine Eq.trans ((Category.assoc (iRB ≫ sB.app j) (c.ι.app j) fB).symm.trans
        ((congrArg (· ≫ fB) (Category.assoc iRB (sB.app j) (c.ι.app j))).trans
          ((congrArg (· ≫ fB) (congrArg (iRB ≫ ·) (Under.w (presU.ι.app j)))).trans
            (Category.assoc iRB _ fB)))) ?_
      ext r
      exact (RingHom.congr_fun hα r).symm
  -- the stage, the étale algebra over it, and the algebra structures of the pushout square
  let instR' : Algebra C (pres₀.diag.obj k : Type u) := (pres₀.diag.obj k).hom.hom.toAlgebra
  let instB'' : Algebra (B ⊗[C] (pres₀.diag.obj k : Type u)) T := ιP.hom.toAlgebra
  let : Algebra (B ⊗[C] (pres₀.diag.obj k : Type u)) (B ⊗[C] Λ) := (c.ι.app k).hom.toAlgebra
  let : Algebra T B' := g.hom.toAlgebra
  let : Algebra (B ⊗[C] (pres₀.diag.obj k : Type u)) B' := (c.ι.app k ≫ fB).hom.toAlgebra
  have : IsScalarTower (B ⊗[C] (pres₀.diag.obj k : Type u)) (B ⊗[C] Λ) B' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (B ⊗[C] (pres₀.diag.obj k : Type u)) T B' :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      congrArg (fun φ : D.obj k ⟶ CommRingCat.of B' ↦ φ.hom x) hsq.w
  have : Algebra.IsPushout (B ⊗[C] (pres₀.diag.obj k : Type u)) (B ⊗[C] Λ) T B' :=
    CommRingCat.isPushout_iff_isPushout.mp hsq
  refine ⟨(pres₀.diag.obj k : Type u), inferInstance, instR', hsmooth k,
    CommRingCat.toAlgHom (pres₀.ι.app k), T, inferInstance, instB'', hιP,
    (Algebra.IsPushout.equiv (B ⊗[C] (pres₀.diag.obj k : Type u)) (B ⊗[C] Λ) T B').symm, v.hom,
    ?_, fun a ↦ ?_⟩
  · ext r
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hv₁) r
  · rw [show α a = algebraMap T B' (v.hom a) from
      (RingHom.congr_fun (congrArg CommRingCat.Hom.hom hv₂) a).symm]
    exact Algebra.IsPushout.equiv_symm_algebraMap_right _ _ _ _ (v.hom a)

/-- **An étale algebra over `B ⊗[C] Λ`, for `Λ` ind-smooth over `R`, is the base change of an
étale algebra over `B ⊗[C] R'` for a single `C`-algebra `R'` smooth over `R`.** Let `Λ` be a
filtered colimit of smooth `R`-algebras, let `C` be an `R`-algebra of finite presentation with an
`R`-algebra map to `Λ`, let `B` be a `C`-algebra and let `B'` be an étale `B ⊗[C] Λ`-algebra.
Then there are a `C`-algebra `R'` whose structure map `R → C → R'` is smooth, a `C`-algebra map
`ρ : R' → Λ`, and an étale `B ⊗[C] R'`-algebra `B''`, such that `B'` is the base change of `B''`
along `1 ⊗ ρ : B ⊗[C] R' → B ⊗[C] Λ`.

In the notation of the proof of Stacks `0CAW` this is "we may assume that `B'` is the base change
of an étale `B ⊗_C R'`-algebra", with `Λ = R^\wedge` and `R'` the smooth stage through which `σ`
factors. The descent of the map `A → B'` that the same step performs is not part of this
statement; for that see
`Stacks.Smoothing.exists_smooth_stage_etale_map_tensorProduct_of_indSmooth`, of which this is
the case `A = R`: the structure map `R → B'` is the only `R`-algebra map `R → B'`, so descending
it says nothing, and the descended `β : R → B''` and its compatibility are discarded. -/
theorem exists_smooth_stage_etale_tensorProduct_of_indSmooth
    (R C Λ : Type u) [CommRing R] [CommRing C] [CommRing Λ] [Algebra R C] [Algebra R Λ]
    [Algebra.FinitePresentation R C] (σ : C →ₐ[R] Λ)
    (B : Type u) [CommRing B] [Algebra C B] (B' : Type u) [CommRing B'] (h : IndSmooth R Λ) :
    letI : Algebra C Λ := σ.toRingHom.toAlgebra
    ∀ [Algebra (B ⊗[C] Λ) B'], Algebra.Etale (B ⊗[C] Λ) B' →
      ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra C R'),
        ((algebraMap C R').comp (algebraMap R C)).Smooth ∧
          ∃ (ρ : R' →ₐ[C] Λ) (B'' : Type u) (_ : CommRing B'')
            (_ : Algebra (B ⊗[C] R') B''), Algebra.Etale (B ⊗[C] R') B'' ∧
            (letI : Algebra (B ⊗[C] R') (B ⊗[C] Λ) :=
                (Algebra.TensorProduct.map (AlgHom.id B B) ρ).toRingHom.toAlgebra;
              Nonempty (B' ≃ₐ[B ⊗[C] Λ] (B ⊗[C] Λ) ⊗[B ⊗[C] R'] B'')) := by
  let : Algebra C Λ := σ.toRingHom.toAlgebra
  intro instB' hetale
  obtain ⟨R', instR'Ring, instR', hsmooth, ρ, B'', instB''Ring, instB'', hEt, e, -, -, -⟩ :=
    exists_smooth_stage_etale_map_tensorProduct_of_indSmooth R C Λ σ B R B' h hetale
      (((algebraMap (B ⊗[C] Λ) B').comp
          ((algebraMap B (B ⊗[C] Λ)).comp (algebraMap C B))).comp (algebraMap R C))
      (RingHom.ext fun _ ↦ rfl)
  exact ⟨R', instR'Ring, instR', hsmooth, ρ, B'', instB''Ring, instB'', hEt, ⟨e⟩⟩

end Stacks.Smoothing

end
