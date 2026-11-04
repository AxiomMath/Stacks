module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.LocallyConstantComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.QuasiCompactFinalObject
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenPoint
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ProetaleTestingFamily
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConnectedConstantModels
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantComplexModelsTransport
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf

/-!
# Pro-étale local invariants on a connected scheme

Let `X` be a connected scheme. Suppose that to the objects `Y` of the small pro-étale site
`X_proét` are attached "local models" `Model Y s`, with values `s` in a type `σ` carrying an
equivalence relation `R`, such that

* a model over `Y` restricts to a model with the same value over every object mapping to `Y`;
* two models over the same nonempty object have values related by `R`;
* every object of `X_proét` has a pro-étale covering by objects carrying a model.

Then all models over nonempty objects have one value up to `R`. This is the connectedness
argument of Stacks 09BI and 09C6: the points of `X` over which some model has a value related to
a given `s` form a subset `Z s` of `X`; two such subsets for unrelated values are disjoint,
because two objects of `X_proét` with points over the same point of `X` have a nonempty fibre
product; the `Z s` cover `X`; and each `Z s` is open. Openness is checked on an affine open `U`
of `X`: a covering of `U` by models is refined by a finite family of affine objects, which is an
fpqc covering of `U`, and the subset of `U` over which the value is related to `s` pulls back to
a clopen subset — everything or nothing — of each member, hence is open (Stacks 03N0). So the
étale site is not needed.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.related_of_apply_eq`: two models over objects with points over
  the same point of `X` have related values.
* `AlgebraicGeometry.Scheme.ProEt.exists_forall_related_of_connectedSpace`: on a connected
  scheme, the values of all models over nonempty objects are related to one value.
* `AlgebraicGeometry.Scheme.ProEt.exists_point_nonempty_fiber_obj`: every nonempty object of
  `X_proét` carries a point of the site, at a point of a weakly contractible affine object
  mapping to it.
* `AlgebraicGeometry.Scheme.ProEt.exists_uniform_constantComplex_representation_of_connectedSpace`:
  on a connected scheme, a bounded object of `D(X_proét, Λ)`, `Λ` Noetherian, with locally
  constant cohomology sheaves of finite type is, pro-étale locally, the constant complex of one
  bounded complex of finite `Λ`-modules (the first step of Stacks 09BI, on `X_proét`).

## References

* [Stacks Project, Tag 09BI](https://stacks.math.columbia.edu/tag/09BI)
* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {σ : Type v} {R : σ → σ → Prop} {Model : X.ProEt → σ → Prop}

/-- **Models over objects with points over one point of `X` have related values.** If `Model`
is stable under restriction and two models over one nonempty object have related values, then
models over `Y₁` and `Y₂` have related values as soon as some points of `Y₁` and `Y₂` have the
same image in `X`: the fibre product `Y₁ ×_X Y₂` is a nonempty object of `X_proét` mapping to
both. -/
theorem related_of_apply_eq
    (hres : ∀ ⦃Y Y' : X.ProEt⦄ (_ : Y' ⟶ Y) ⦃s : σ⦄, Model Y s → Model Y' s)
    (huniq : ∀ (Y : X.ProEt) (_ : Y.left) ⦃s t : σ⦄, Model Y s → Model Y t → R s t)
    {Y₁ Y₂ : X.ProEt} {s t : σ} (h₁ : Model Y₁ s) (h₂ : Model Y₂ t) (y₁ : Y₁.left)
    (y₂ : Y₂.left) (h : Y₁.hom y₁ = Y₂.hom y₂) : R s t := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y₁ y₂ h
  have : WeaklyEtale Y₂.hom := Y₂.prop
  have : WeaklyEtale Y₁.hom := Y₁.prop
  let V : X.ProEt := ProEt.mk (pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom)
  let a : V ⟶ Y₁ := MorphismProperty.Over.homMk (pullback.fst Y₁.hom Y₂.hom) rfl trivial
  let b : V ⟶ Y₂ := MorphismProperty.Over.homMk (pullback.snd Y₁.hom Y₂.hom)
    (pullback.condition (f := Y₁.hom) (g := Y₂.hom)).symm trivial
  exact huniq V z (hres a h₁) (hres b h₂)

variable (hR : Equivalence R)
  (hres : ∀ ⦃Y Y' : X.ProEt⦄ (_ : Y' ⟶ Y) ⦃s : σ⦄, Model Y s → Model Y' s)
  (huniq : ∀ (Y : X.ProEt) (_ : Y.left) ⦃s t : σ⦄, Model Y s → Model Y t → R s t)
  (hloc : ∀ U : X.ProEt, ∃ S ∈ ProEt.topology X U,
    ∀ ⦃W : X.ProEt⦄ ⦃g : W ⟶ U⦄, S g → ∃ s, Model W s)

include hR hres huniq hloc

/-- The points of `X` lying under a point of an object carrying a model whose value is related
to `s` form an open subset of `X`. -/
theorem isOpen_setOf_exists_model (s : σ) :
    IsOpen {x : X | ∃ (Y : X.ProEt) (y : Y.left) (t : σ), Model Y t ∧ R t s ∧ Y.hom y = x} := by
  classical
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨Y, y, t, hYt, hts, rfl⟩
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := Y.hom y)
    (U := ⊤) trivial
  let T : X.ProEt := ofAffineOpen ⟨U, hU⟩
  have : IsAffine T.left := hU
  obtain ⟨S, hS, hSm⟩ := hloc T
  obtain ⟨E, hfin, hE, hle, hEa⟩ := AlgebraicGeometry.ProEtale.exists_indEtale_covering_le S hS
  choose s' hs' using fun k => hSm (hle _ (E.sieve₀_f k))
  have hw : ∀ k, (E.f k).left ≫ T.hom = (E.X k).hom := fun k => MorphismProperty.Over.w (E.f k)
  have hwe : ∀ k, WeaklyEtale (E.f k).left := fun k => by
    have h₁ : WeaklyEtale ((E.f k).left ≫ T.hom) := by
      rw [hw]
      exact (E.X k).prop
    have : WeaklyEtale T.hom := T.prop
    exact MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) _ T.hom this h₁
  have hhom : ∀ k (e : (E.X k).left), (E.X k).hom e = T.hom ((E.f k).left e) := fun k e => by
    rw [← hw k]
    exact Scheme.Hom.comp_apply _ _ e
  have hsurj : ∀ p : T.left, ∃ k, p ∈ Set.range (E.f k).left := fun p => by
    obtain ⟨V, g, hg, z, rfl⟩ := exists_mem_range_of_mem_topology hE p
    obtain ⟨_, a, _, ⟨k⟩, rfl⟩ := hg
    exact ⟨k, a.left z, (Scheme.Hom.comp_apply _ _ z).symm⟩
  have hfpqc : Presieve.ofArrows (fun k => (E.X k).left) (fun k => (E.f k).left) ∈
      Scheme.fpqcPrecoverage T.left :=
    Scheme.ofArrows_mem_fpqcPrecoverage_of_finite_index inferInstance _ _ (fun k => (hEa k).1)
      (fun k => (hwe k).flat) hsurj
  let W : ∀ k, (E.X k).left.Opens := fun k => if R (s' k) s then ⊤ else ⊥
  have hrel : ∀ k l (z : ↑(pullback (E.f k).left (E.f l).left)), R (s' k) (s' l) := by
    intro k l z
    refine related_of_apply_eq hres huniq (hs' k) (hs' l)
      (pullback.fst (E.f k).left (E.f l).left z) (pullback.snd (E.f k).left (E.f l).left z) ?_
    rw [hhom, hhom]
    exact congrArg T.hom (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      pullback.condition])
  obtain ⟨V, hV, -⟩ := existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage _ _ hfpqc W
    fun k l => by
      ext z
      have hkl : R (s' k) s ↔ R (s' l) s :=
        ⟨hR.trans (hR.symm (hrel k l z)), hR.trans (hrel k l z)⟩
      by_cases hl : R (s' l) s <;> simp [W, hkl, hl]
  have hmem : ∀ k e, e ∈ (E.f k).left ⁻¹ᵁ V ↔ R (s' k) s := fun k e => by
    rw [hV k]
    by_cases hk : R (s' k) s <;> simp [W, hk]
  refine ⟨T.hom '' (V : Set T.left), ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨k, e, rfl⟩ := hsurj p
    exact ⟨E.X k, e, s' k, hs' k, (hmem k e).1 hp, hhom k e⟩
  · have : IsOpenImmersion T.hom := inferInstanceAs (IsOpenImmersion U.ι)
    exact T.hom.isOpenEmbedding.isOpenMap _ V.isOpen
  · obtain ⟨p, hp⟩ : Y.hom y ∈ Set.range T.hom := by
      show Y.hom y ∈ Set.range U.ι
      rw [Scheme.Opens.range_ι]
      exact hxU
    obtain ⟨k, e, rfl⟩ := hsurj p
    have hk : R (s' k) s := hR.trans (related_of_apply_eq hres huniq (hs' k) hYt e y
      ((hhom k e).trans hp)) hts
    refine ⟨(E.f k).left e, ?_, hp⟩
    exact (hmem k e).2 hk

/-- **On a connected scheme a pro-étale local invariant has one value.** Let `X` be a connected
scheme and `Model` a family of "local models" over the objects of `X_proét`, with values in a
type carrying an equivalence relation `R`, which restrict along morphisms, have related values
over one nonempty object, and exist over the members of a covering of every object. Then there
is a value `s₀` to which the value of every model over a nonempty object is related.

The subsets `Z s` of `X` lying under objects carrying models with values related to `s` are
open (`isOpen_setOf_exists_model`), cover `X`, and two of them for unrelated values are disjoint
(`related_of_apply_eq`); so the one containing a chosen point is clopen, hence everything. -/
theorem exists_forall_related_of_connectedSpace [ConnectedSpace X] :
    ∃ s₀ : σ, ∀ (Y : X.ProEt) (_ : Y.left) ⦃s : σ⦄, Model Y s → R s s₀ := by
  classical
  let Z : σ → Set X := fun s =>
    {x : X | ∃ (Y : X.ProEt) (y : Y.left) (t : σ), Model Y t ∧ R t s ∧ Y.hom y = x}
  have hcov : ∀ x : X, ∃ s, x ∈ Z s := fun x => by
    obtain ⟨S, hS, hSm⟩ := hloc (ProEt.mk (𝟙 X))
    obtain ⟨Y, g, hg, y, rfl⟩ := exists_mem_range_of_mem_topology hS x
    obtain ⟨s, hs⟩ := hSm hg
    have hgY : g.left = Y.hom := (Category.comp_id _).symm.trans (MorphismProperty.Over.w g)
    exact ⟨s, Y, y, s, hs, hR.refl s, by rw [hgY]; rfl⟩
  have hdisj : ∀ (x : X) (s t : σ), x ∈ Z s → x ∈ Z t → R s t := by
    rintro x s t ⟨Y, y, s', hs', hs's, rfl⟩ ⟨Y', y', t', ht', ht't, hy'⟩
    exact hR.trans (hR.symm hs's)
      (hR.trans (related_of_apply_eq hres huniq hs' ht' y y' hy'.symm) ht't)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨s₀, hx₀⟩ := hcov x₀
  have hcompl : (Z s₀)ᶜ = ⋃ (s : σ) (_ : ¬ R s s₀), Z s := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      obtain ⟨s, hs⟩ := hcov x
      refine ⟨s, fun h => hx ?_, hs⟩
      obtain ⟨Y, y, t, ht, hts, hy⟩ := hs
      exact ⟨Y, y, t, ht, hR.trans hts h, hy⟩
    · rintro ⟨s, hs, hx⟩ hx₀'
      exact hs (hdisj x s s₀ hx hx₀')
  have hclopen : IsClopen (Z s₀) := by
    refine ⟨?_, isOpen_setOf_exists_model hR hres huniq hloc s₀⟩
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion fun s => isOpen_iUnion fun _ =>
      isOpen_setOf_exists_model hR hres huniq hloc s
  have huniv : Z s₀ = Set.univ := hclopen.eq_univ ⟨x₀, hx₀⟩
  refine ⟨s₀, fun Y y s hs => ?_⟩
  exact hdisj _ s s₀ ⟨Y, y, s, hs, hR.refl s, rfl⟩ (huniv ▸ Set.mem_univ _)

omit hR hres huniq hloc

/-- **Every nonempty object of `X_proét` carries a point of the site.** An affine object `W`
with w-contractible ring of global sections maps to `Y` and has a point `w` (`Y` is covered by
such objects, Stacks 098I); the point of `X_proét` at `w` (`clopenPointOver`) has a nonempty
fibre at `W`, hence at `Y`. -/
theorem exists_point_nonempty_fiber_obj.{w} {Y : X.ProEt} (y : Y.left) :
    ∃ p : (ProEt.topology X).Point.{max (u + 1) w}, Nonempty (p.fiber.obj Y) := by
  obtain ⟨I, V, f, hcov, hV⟩ := hasEnoughObjects_isAffineWContractible (S := X) Y
  obtain ⟨Z, g, hg, z, -⟩ := exists_mem_range_of_mem_topology hcov y
  obtain ⟨_, a, _, ⟨i⟩, -⟩ := hg
  have := (hV i).1
  obtain ⟨t⟩ := nonempty_clopenPointOver_fiber_obj.{w} (V i) (hV i).2 (a.left z)
  exact ⟨clopenPointOver.{w} (V i) (hV i).2 (a.left z),
    ⟨(clopenPointOver.{w} (V i) (hV i).2 (a.left z)).fiber.map (f i) t⟩⟩

section ConstantModels

attribute [local instance] HasDerivedCategory.standard

variable (R : Type (max (u + 1) v)) [CommRing R]

/-- Presheaves of `R`-modules on `X_proét` admit sheafification. -/
local instance hasSheafify_proEt_moduleCat' :
    HasSheafify (ProEt.topology X) (ModuleCat.{max (u + 1) v} R) :=
  hasSheafify_moduleCat.{u + 1, u, v, max (u + 1) v} _ _

/-- Presheaves of `R`-modules on the slice of `X_proét` over `U` admit sheafification. -/
local instance hasSheafify_proEt_over_moduleCat' (U : X.ProEt) :
    HasSheafify ((ProEt.topology X).over U) (ModuleCat.{max (u + 1) v} R) :=
  hasSheafify_moduleCat.{u + 1, u, v, max (u + 1) v} _ _

/-- Restriction of sheaves to a slice of `X_proét` is additive. -/
local instance additive_overPullback_proEt (W : X.ProEt) :
    ((ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v} R) W).Additive := by
  have : PreservesFiniteLimits ((ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v} R) W ⋙
      sheafToPresheaf ((ProEt.topology X).over W) (ModuleCat.{max (u + 1) v} R)) := by
    change PreservesFiniteLimits (sheafToPresheaf (ProEt.topology X) _ ⋙
      (Functor.whiskeringLeft _ _ _).obj (Over.forget W).op)
    infer_instance
  have : PreservesFiniteLimits
      ((ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v} R) W) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  exact Functor.additive_of_preserves_binary_products _

/-- A constant model over an object of `X_proét` restricts along a morphism. -/
theorem nonempty_constantComplexModel_of_hom
    (T : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{max (u + 1) v} R)) ℤ)
    {Y Y' : X.ProEt} (g : Y' ⟶ Y) {P : CochainComplex (ModuleCat.{max (u + 1) v} R) ℤ}
    (e : Nonempty (DerivedCategory.Q.obj
        ((((ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v} R) Y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf ((ProEt.topology X).over Y)
          (ModuleCat.{max (u + 1) v} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) :
    Nonempty (DerivedCategory.Q.obj
        ((((ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v} R) Y').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf ((ProEt.topology X).over Y')
          (ModuleCat.{max (u + 1) v} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  let A := ModuleCat.{max (u + 1) v} R
  have : ((ProEt.topology X).overMapPullback A g).IsLeftAdjoint :=
    ((Over.mapPullbackAdj g).sheafPushforwardContinuous ((ProEt.topology X).over Y')
      ((ProEt.topology X).over Y)).isLeftAdjoint
  have : ((ProEt.topology X).overMapPullback A g).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact Stacks.ConstantSheaf.exists_constantComplexModel_of_hom (ProEt.topology X) A g T P e.some

variable [IsNoetherianRing R]

/-- **One constant complex model on a connected scheme (the first step of Stacks 09BI on
`X_proét`).** Let `X` be a connected scheme, `R` a Noetherian ring and `K` a bounded object of
`D(X_proét, R)` whose cohomology sheaves are locally constant of finite type. There are a complex
`T` representing `K` and a bounded complex `P` of finite `R`-modules such that every object `U`
of `X_proét` has a covering sieve all of whose members are nonempty and carry an isomorphism
`T|_W ≅ \underline{P}` in `D(X_proét/W, R)`.

Locally such models exist (Stacks 094G); two models over a nonempty object have isomorphic
complexes of coefficients, as is seen at a point of the site lifting to it
(`exists_point_nonempty_fiber_obj`); and the connectedness argument
`exists_forall_related_of_connectedSpace` makes the coefficients of all models over nonempty
objects isomorphic to one of them. Empty members of a covering may be dropped. -/
theorem exists_uniform_constantComplex_representation_of_connectedSpace [ConnectedSpace X]
    (K : DerivedCategory.Bounded (Sheaf (ProEt.topology X) (ModuleCat.{max (u + 1) v} R)))
    (hK : ∀ n : ℤ,
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max (u + 1) v}
        (ProEt.topology X) R
        ((DerivedCategory.homologyFunctor (Sheaf (ProEt.topology X)
          (ModuleCat.{max (u + 1) v} R)) n).obj K.obj)) :
    ∃ (T : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{max (u + 1) v} R)) ℤ)
      (_e : K.obj ≅ DerivedCategory.Q.obj T)
      (P : CochainComplex (ModuleCat.{max (u + 1) v} R) ℤ) (a b : ℤ),
      (∀ n, n ∉ Set.Icc a b → IsZero (P.X n)) ∧ (∀ n, ModuleCat.isFG R (P.X n)) ∧
      ∀ U : X.ProEt, ∃ (ι : Type (u + 1)) (W : ι → X.ProEt) (g : ∀ j, W j ⟶ U),
        Sieve.ofArrows W g ∈ ProEt.topology X U ∧ ∀ j, Nonempty (W j).left ∧
          Nonempty (DerivedCategory.Q.obj
            ((((ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v} R)
              (W j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj T) ≅
          DerivedCategory.Q.obj
            (((constantSheaf ((ProEt.topology X).over (W j))
              (ModuleCat.{max (u + 1) v} R)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) := by
  classical
  let J := ProEt.topology X
  let A := ModuleCat.{max (u + 1) v} R
  obtain ⟨T, e, I, V, f, hcov, hmodel⟩ :=
    Stacks.ConstantSheaf.exists_cover_constantComplex_representation' J R (ProEt.mk (𝟙 X)) K hK
  -- values: bounded complexes of finite modules; relation: isomorphism in `D(R)`
  let σ := {P : CochainComplex A ℤ // ∃ a b : ℤ, (∀ n, n ∉ Set.Icc a b → IsZero (P.X n)) ∧
    ∀ n, ModuleCat.isFG R (P.X n)}
  let Rel : σ → σ → Prop := fun P Q =>
    Nonempty (DerivedCategory.Q.obj P.1 ≅ DerivedCategory.Q.obj Q.1)
  let Model : X.ProEt → σ → Prop := fun W P => Nonempty (DerivedCategory.Q.obj
    (((J.overPullback A W).mapHomologicalComplex (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (J.over W) A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.1))
  have hRel : Equivalence Rel :=
    ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩
  have hres : ∀ ⦃Y Y' : X.ProEt⦄ (_ : Y' ⟶ Y) ⦃s : σ⦄, Model Y s → Model Y' s :=
    fun _ _ g _ h => nonempty_constantComplexModel_of_hom R T g h
  have huniq : ∀ (Y : X.ProEt) (_ : Y.left) ⦃s t : σ⦄, Model Y s → Model Y t → Rel s t := by
    intro Y y s t ⟨es⟩ ⟨et⟩
    obtain ⟨p, ⟨x⟩⟩ := exists_point_nonempty_fiber_obj.{u, v} y
    exact Stacks.ConstantSheaf.exists_iso_of_constantComplexModels_of_point' J R p x x T s.1 t.1
      es et
  have hloc : ∀ U : X.ProEt, ∃ S ∈ ProEt.topology X U,
      ∀ ⦃W : X.ProEt⦄ ⦃g : W ⟶ U⦄, S g → ∃ s, Model W s := by
    intro U
    refine ⟨(Sieve.ofArrows V f).pullback (isTerminal_mk_id.from U),
      J.pullback_stable _ hcov, fun W g hg => ?_⟩
    obtain ⟨_, a, _, ⟨i⟩, -⟩ := hg
    obtain ⟨P, a', b', hPv, hPfg, hP⟩ := hmodel i
    exact ⟨⟨P, a', b', hPv, hPfg⟩, hres a hP⟩
  obtain ⟨s₀, hs₀⟩ := exists_forall_related_of_connectedSpace hRel hres huniq hloc
  obtain ⟨a, b, hP₀v, hP₀fg⟩ := s₀.2
  refine ⟨T, e, s₀.1, a, b, hP₀v, hP₀fg, fun U => ?_⟩
  obtain ⟨S, hS, hSm⟩ := hloc U
  let ι := Σ W : X.ProEt, {g : W ⟶ U // Nonempty W.left ∧ Model W s₀}
  refine ⟨ι, fun j => j.1, fun j => j.2.1, ?_, fun j => j.2.2⟩
  refine J.transitive hS _ fun W g hg => ?_
  rcases isEmpty_or_nonempty W.left with hW | hW
  · exact J.superset_covering bot_le (bot_mem_topology_of_isEmpty W hW)
  · obtain ⟨w⟩ := hW
    obtain ⟨s, hs⟩ := hSm hg
    obtain ⟨es⟩ := hs₀ W w hs
    have hW₀ : Model W s₀ := by
      have : (constantSheaf (J.over W) A).Additive := by unfold constantSheaf; infer_instance
      have : PreservesFiniteLimits (constantSheaf (J.over W) A) := by
        unfold constantSheaf; infer_instance
      have : PreservesFiniteColimits (constantSheaf (J.over W) A) := by
        unfold constantSheaf; infer_instance
      obtain ⟨e₁⟩ := hs
      exact ⟨e₁ ≪≫ ((constantSheaf (J.over W) A).mapDerivedCategoryFactors.app s.1).symm ≪≫
        (constantSheaf (J.over W) A).mapDerivedCategory.mapIso es ≪≫
          (constantSheaf (J.over W) A).mapDerivedCategoryFactors.app s₀.1⟩
    have hmem : Sieve.ofArrows (fun j : ι => j.1) (fun j => j.2.1) g :=
      Sieve.ofArrows_mk _ _ (⟨W, g, ⟨w⟩, hW₀⟩ : ι)
    rw [Sieve.pullback_eq_top_of_mem _ hmem]
    exact J.top_mem W

end ConstantModels

end AlgebraicGeometry.Scheme.ProEt

end
