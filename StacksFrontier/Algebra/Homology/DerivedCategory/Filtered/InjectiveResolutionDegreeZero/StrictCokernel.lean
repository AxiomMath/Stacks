module

public import StacksCore.CategoryTheory.Filtration.Strict
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveSplitting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cokernels of strict morphisms of filtered objects

Auxiliary material for `InjectiveResolutionDegreeZero`: filtrations built from a family of steps,
a pullback criterion for squares of monomorphisms, and the cokernel of a strict morphism of
filtered objects together with its filtration, its graded pieces and the short exact sequences
they form.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredInjectiveResolutionDegreeZero

namespace CochainComplex.FilteredInjective.Resolution

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

section Auxiliary

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- A morphism of filtered objects whose underlying morphism vanishes has vanishing components on
the filtration steps: the steps are subobjects, so a component is determined by the underlying
morphism. -/
public lemma natTrans_app_eq_zero {A B : FilteredObject 𝒜 ℤᵒᵖ} (f : A ⟶ B) (hf : f.hom = 0)
    (i : ℤᵒᵖ) : f.natTrans.app i = 0 := by
  rw [← cancel_mono (B.filtration.ι.app i), f.comm i, hf, comp_zero, zero_comp]

attribute [local simp] CochainComplex.evalFil_ι_app

/-- A zero object of `CochainComplex 𝒜 ℤ` is zero in every degree. -/
private lemma isZero_X_of_isZero {Z : CochainComplex 𝒜 ℤ} (hZ : IsZero Z) (n : ℤ) :
    IsZero (Z.X n) := by
  rw [IsZero.iff_id_eq_zero] at hZ ⊢
  simpa using congrArg (fun f => HomologicalComplex.Hom.f f n) hZ

/-- The filtration of a filtered complex with finite filtration is finite in every degree. -/
private lemma isFinite_eval {K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (hK : K.filtration.IsFinite) (n : ℤ) : (evalFil K n).filtration.IsFinite := by
  refine .of_exists ?_ ?_
  · obtain ⟨p, hp⟩ := hK.exists_isIso_ι
    refine ⟨p, ?_⟩
    show IsIso ((K.filtration.ι.app (op p)).f n)
    exact inferInstanceAs
      (IsIso ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n).map (K.filtration.ι.app (op p))))
  · obtain ⟨q, hq⟩ := hK.exists_isZero_obj
    exact ⟨q, isZero_X_of_isZero hq n⟩

end Auxiliary

section Steps

variable {C : Type u} [Category.{v} C]

/-- A `ℤ`-indexed family of subobjects of `X` with a morphism `F^{p + 1} ⟶ F^p` over `X` for every
`p` has a morphism `F^p ⟶ F^q` over `X` whenever `q ≤ p`. -/
private lemma nonempty_hom_of_steps {X : C} (F : ℤ → MonoOver X)
    (s : ∀ p : ℤ, Nonempty (F (p + 1) ⟶ F p)) {p q : ℤ} (hqp : q ≤ p) :
    Nonempty (F p ⟶ F q) := by
  induction p, hqp using Int.leInduction with
  | base => exact ⟨𝟙 _⟩
  | succ n _ ih => exact ⟨(s n).some ≫ ih.some⟩

/-- The decreasing filtration of `X` given by a `ℤ`-indexed family `F` of subobjects of `X` that
decreases in the sense that `F^p` maps to `F^q` over `X` whenever `q ≤ p`.

No coherence is asked of those maps, and none is possible to ask: `MonoOver X` is a thin category,
so a morphism `F^p ⟶ F^q` over `X` is unique if it exists and the functoriality of `p ↦ F^p` is
automatic. By `nonempty_hom_of_steps` the hypothesis follows from the individual steps
`F^{p + 1} ⟶ F^p`. -/
noncomputable def filtrationOfSteps {X : C} (F : ℤ → MonoOver X)
    (h : ∀ p q : ℤ, q ≤ p → Nonempty (F p ⟶ F q)) : Filtration X ℤᵒᵖ where
  toMonoOver :=
    { obj := fun i => F i.unop
      map := fun {i j} f => (h i.unop j.unop (leOfHom f.unop)).some
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }

/-- The `p`-th step of a filtration built by `filtrationOfSteps` is the subobject `F^p`. -/
@[local simp]
lemma filtrationOfSteps_ι_app {X : C} (F : ℤ → MonoOver X)
    (h : ∀ p q : ℤ, q ≤ p → Nonempty (F p ⟶ F q)) (p : ℤ) :
    (filtrationOfSteps F h).ι.app (op p) = (F p).obj.hom :=
  rfl

/-- The map of a filtration built by `filtrationOfSteps` is the underlying map of *any* morphism
`F^p ⟶ F^q` over `X`, there being only one. -/
private lemma filtrationOfSteps_diagram_map {X : C} (F : ℤ → MonoOver X)
    (h : ∀ p q : ℤ, q ≤ p → Nonempty (F p ⟶ F q)) {p q : ℤ} (hqp : q ≤ p) (t : F p ⟶ F q) :
    (filtrationOfSteps F h).diagram.map (homOfLE hqp).op =
      (MonoOver.forget X ⋙ Over.forget X).map t :=
  congrArg (fun m : F p ⟶ F q => (MonoOver.forget X ⋙ Over.forget X).map m)
    (Subsingleton.elim _ t)

end Steps

section IsPullback

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A criterion for a square of monomorphisms to be a pullback square, in the form in which
strictness of a morphism of filtered objects is verified: if the subobject `I' ⟶ I` is killed by
`w : I ⟶ Q` and every map to `A` killed by `u ≫ w` factors through the subobject `A' ⟶ A`, then
`A' = u^{-1} I'`.

In the situation of [Stacks, Tag 05TS] `I` is a finite direct sum, `I'` the partial sum `F^p I`,
`w` the projection to the complementary summand, and the hypothesis on `A` says that `F^p A` is the
kernel of `A ⟶ A / F^p A ⟶ I^{p - 1}`, the second map being one of the chosen injections. -/
private lemma isPullback_of_factorsThru {A' A I' I Q : C}
    (v : A' ⟶ I') (iA : A' ⟶ A) (iI : I' ⟶ I) (u : A ⟶ I) (w : I ⟶ Q)
    (comm : v ≫ iI = iA ≫ u) [Mono iA] [Mono iI] (hw : iI ≫ w = 0)
    (hA : ∀ ⦃T : C⦄ (x : T ⟶ A), x ≫ u ≫ w = 0 → ∃ y : T ⟶ A', y ≫ iA = x) :
    IsPullback v iA iI u := by
  have key : ∀ s : PullbackCone iI u, s.snd ≫ u ≫ w = 0 := fun s => by
    rw [← Category.assoc, ← s.condition, Category.assoc, hw, comp_zero]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm
    (fun s => (hA s.snd (key s)).choose) (fun s => ?_)
    (fun s => (hA s.snd (key s)).choose_spec) (fun s m _ h₂ => ?_))
  · rw [← cancel_mono iI, Category.assoc, comm, ← Category.assoc,
      (hA s.snd (key s)).choose_spec, s.condition]
  · rw [← cancel_mono iA, h₂, (hA s.snd (key s)).choose_spec]

end IsPullback

section Cokernel

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- A finite filtration has a pair of bounds: an index `a` at which it exhausts its ambient object
and an index `b + 1 > a` at which it vanishes. This is the `a ≤ b` with which the source's
construction of a filtered injective object begins. -/
private lemma exists_bounds {X : 𝒜} (F : Filtration X ℤᵒᵖ) (hF : F.IsFinite) :
    ∃ a b : ℤ, a ≤ b ∧ IsIso (F.ι.app (op a)) ∧ IsZero (F.obj (op (b + 1))) := by
  obtain ⟨p, hp⟩ := hF.exists_isIso_ι
  obtain ⟨q, hq⟩ := hF.exists_isZero_obj
  exact ⟨min p q, max p q, min_le_max, Filtration.isIso_ι_app_of_le F (min_le_left p q) hp,
    Filtration.isZero_obj_of_le F (le_trans (le_max_right p q) (Int.le_add_one le_rfl)) hq⟩

/-- The `i`-th step of the quotient filtration on the cokernel of a strict morphism `u : A ⟶ I` of
filtered objects: the image of `F^i I` in `Coker(u)`, realised as `F^i I / F^i A` and included in
`Coker(u) = I / A` by the map the inclusions `F^i A ⟶ A`, `F^i I ⟶ I` induce on cokernels. -/
public noncomputable def cokernelStep {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) (i : ℤᵒᵖ) :
    cokernel (u.natTrans.app i) ⟶ cokernel u.hom :=
  cokernel.map _ _ (A.filtration.ι.app i) (I.filtration.ι.app i) (u.comm i)

/-- Strictness of `u` at `i` is exactly what makes `F^i I / F^i A ⟶ I / A` a monomorphism: the
square defining it is a pullback square. -/
public instance mono_cokernelStep {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u]
    (i : ℤᵒᵖ) : Mono (cokernelStep u i) :=
  Abelian.mono_cokernel_map_of_isPullback (IsStrictHom.isPullback u i)

/-- The quotient filtration of `Coker(u)` is functorial: the square
`F^i I / F^i A ⟶ F^j I / F^j A`, `F^i Coker(u) ⟶ F^j Coker(u)` commutes over `Coker(u)`. -/
public lemma cokernelStep_naturality {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) {i j : ℤᵒᵖ}
    (f : i ⟶ j) :
    cokernel.map _ _ (A.filtration.diagram.map f) (I.filtration.diagram.map f)
        (u.natTrans.naturality f).symm ≫ cokernelStep u j = cokernelStep u i := by
  apply coequalizer.hom_ext
  simp only [cokernelStep, cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc]
  rw [← Category.assoc, Filtration.diagram_map_comp_ι_app]

/-- The quotient filtration on the cokernel of a strict morphism `u : A ⟶ I` of filtered objects:
the subobject `F^i Coker(u) = F^i I / F^i A` of `Coker(u)`, functorially in `i`. -/
@[ega "0 13.5.1" "more general"]
public noncomputable def cokernelFiltration {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I)
    [IsStrictHom u] : ℤᵒᵖ ⥤ MonoOver (cokernel u.hom) where
  obj i := MonoOver.mk (cokernelStep u i)
  map f := MonoOver.homMk
    (cokernel.map _ _ (A.filtration.diagram.map f) (I.filtration.diagram.map f)
      (u.natTrans.naturality f).symm) (cokernelStep_naturality u f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The cokernel of a strict morphism `u : A ⟶ I` of filtered objects, as a filtered object: the
cokernel of `u` in `𝒜` with the quotient filtration `F^p Coker(u) = F^p I / F^p A`.

This is the cokernel of `u` in `Fil(𝒜)`; it is recorded here only as far as the construction of a
filtered injective resolution uses it, namely with `cokernelπ` and the two lemmas below. -/
@[implicit_reducible, ega "0 13.5.1" "more general"]
public noncomputable def cokernelObj {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u] :
    FilteredObject 𝒜 ℤᵒᵖ where
  X := cokernel u.hom
  filtration := ⟨cokernelFiltration u⟩

@[local simp]
private lemma cokernelObj_filtration_ι_app {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I)
    [IsStrictHom u] (i : ℤᵒᵖ) : (cokernelObj u).filtration.ι.app i = cokernelStep u i := rfl

/-- The `i`-th step of the quotient filtration receives `F^i I`, compatibly with `Coker(u)`
receiving `I`. -/
public lemma π_comp_cokernelStep {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) (i : ℤᵒᵖ) :
    cokernel.π (u.natTrans.app i) ≫ cokernelStep u i =
      I.filtration.ι.app i ≫ cokernel.π u.hom := by
  simp only [cokernelStep, cokernel.π_desc]

/-- The projection of a filtered object onto the cokernel of a strict morphism into it. -/
public noncomputable def cokernelπ {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u] :
    I ⟶ cokernelObj u :=
  FilteredObject.homMk (cokernel.π u.hom) (fun i => cokernel.π (u.natTrans.app i))
    (fun i => π_comp_cokernelStep u i)

@[local simp]
private lemma cokernelπ_hom {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u] :
    (cokernelπ u).hom = cokernel.π u.hom := rfl

private lemma cokernelπ_natTrans_app {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u]
    (i : ℤᵒᵖ) : (cokernelπ u).natTrans.app i = cokernel.π (u.natTrans.app i) := rfl

/-- The projection onto the cokernel kills the subobject it divides by, on underlying objects. -/
private lemma hom_comp_cokernelπ_hom {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u] :
    u.hom ≫ (cokernelπ u).hom = 0 := cokernel.condition _

/-- The projection onto the cokernel kills the subobject it divides by, on each filtration step. -/
private lemma natTrans_app_comp_cokernelπ_natTrans_app {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I)
    [IsStrictHom u] (i : ℤᵒᵖ) : u.natTrans.app i ≫ (cokernelπ u).natTrans.app i = 0 :=
  cokernel.condition _

/-- `u ≫ cokernelπ u = 0`: the projection kills the subobject it divides by. -/
private lemma comp_cokernelπ_hom {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u] :
    (u ≫ cokernelπ u).hom = 0 := by
  show u.hom ≫ cokernel.π u.hom = 0
  exact cokernel.condition _

/-- The quotient filtration of the cokernel of a strict morphism between finitely filtered objects
is again finite. -/
lemma cokernelObj_filtration_isFinite {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I)
    [IsStrictHom u] (hI : I.filtration.IsFinite) : (cokernelObj u).filtration.IsFinite := by
  refine .of_exists ?_ ?_
  · obtain ⟨p, hp⟩ := hI.exists_isIso_ι
    refine ⟨p, ?_⟩
    rw [cokernelObj_filtration_ι_app]
    have := epi_of_epi_fac (π_comp_cokernelStep u (op p))
    exact isIso_of_mono_of_epi (cokernelStep u (op p))
  · obtain ⟨q, hq⟩ := hI.exists_isZero_obj
    refine ⟨q, ?_⟩
    show IsZero (cokernel (u.natTrans.app (op q)))
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (cokernel.π (u.natTrans.app (op q))), comp_zero,
      Category.comp_id]
    exact hq.eq_of_src _ _

omit [Abelian 𝒜] in
/-- The square `F^{p + 1} A ⟶ F^p A`, `F^{p + 1} I ⟶ F^p I` cut out of a strict morphism
`u : A ⟶ I` of filtered objects is a pullback square: `F^{p + 1} I ∩ F^p A = F^{p + 1} A` inside
`I`, by strictness at `p` and at `p + 1`. -/
private lemma isPullback_diagram_map {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u]
    (p : ℤ) :
    IsPullback (A.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
      (u.natTrans.app (op (p + 1))) (u.natTrans.app (op p))
      (I.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) := by
  refine IsPullback.of_right ?_ (u.natTrans.naturality _) (IsStrictHom.isPullback u (op p)).flip
  rw [Filtration.diagram_map_comp_ι_app, Filtration.diagram_map_comp_ι_app]
  exact (IsStrictHom.isPullback u (op (p + 1))).flip

/-- **Stacks 0127, the injective half.** The graded pieces of a strict morphism of filtered objects
are monomorphisms. -/
private lemma mono_gradedPiece_map {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u]
    (p : ℤ) : Mono ((gr p).map u) :=
  Abelian.mono_cokernel_map_of_isPullback (isPullback_diagram_map u p)

/-! ### Cokernels commute with cokernels -/

/-- **Cokernels commute with cokernels.** In a commuting square `π₁ ≫ vZ = vY ≫ cokernel.π f₀`
whose left-hand column `π₁` is an epimorphism, the map `dZ : Coker(vY) ⟶ Coker(vZ)` determined by
`cokernel.π vY ≫ dZ = cokernel.π f₀ ≫ cokernel.π vZ` is a cokernel of the map
`dY : Coker(vX) ⟶ Coker(vY)` determined by `cokernel.π vX ≫ dY = f₀ ≫ cokernel.π vY`.

Nothing of exactness is used: `Coker(vZ)` is a colimit of a diagram of colimits, computed in the
other order. This is the right-exact half of [Stacks, Tag 0127]. -/
private noncomputable def isColimit_cokernelCofork_of_cokernel_π {X₀ X₁ Y₀ Y₁ Z₁ : 𝒜}
    {f₀ : X₀ ⟶ Y₀} {vX : X₁ ⟶ X₀} {vY : Y₁ ⟶ Y₀} {π₁ : Y₁ ⟶ Z₁} [Epi π₁]
    {vZ : Z₁ ⟶ cokernel f₀} (hsq : π₁ ≫ vZ = vY ≫ cokernel.π f₀)
    {dY : cokernel vX ⟶ cokernel vY} {dZ : cokernel vY ⟶ cokernel vZ}
    (hdY : cokernel.π vX ≫ dY = f₀ ≫ cokernel.π vY)
    (hdZ : cokernel.π vY ≫ dZ = cokernel.π f₀ ≫ cokernel.π vZ)
    (w : dY ≫ dZ = 0) : IsColimit (CokernelCofork.ofπ dZ w) := by
  have hepi : Epi dZ := epi_of_epi_fac hdZ
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {T} t ht => ?_)
  have h1 : f₀ ≫ cokernel.π vY ≫ t = 0 := by
    rw [← Category.assoc, ← hdY, Category.assoc, ht, comp_zero]
  have h2 : vZ ≫ cokernel.desc f₀ (cokernel.π vY ≫ t) h1 = 0 := by
    rw [← cancel_epi π₁, ← Category.assoc, hsq, Category.assoc, cokernel.π_desc,
      ← Category.assoc, cokernel.condition, zero_comp, comp_zero]
  refine ⟨cokernel.desc vZ (cokernel.desc f₀ (cokernel.π vY ≫ t) h1) h2, ?_⟩
  rw [← cancel_epi (cokernel.π vY), ← Category.assoc, hdZ, Category.assoc, cokernel.π_desc,
    cokernel.π_desc]

/-- The quotient filtration is functorial through the cokernel projections: the square
`F^i I ⟶ F^j I`, `F^i Coker(u) ⟶ F^j Coker(u)` commutes. -/
private lemma π_comp_cokernelObj_diagram_map {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I)
    [IsStrictHom u] {i j : ℤᵒᵖ} (f : i ⟶ j) :
    cokernel.π (u.natTrans.app i) ≫ (cokernelObj u).filtration.diagram.map f =
      I.filtration.diagram.map f ≫ cokernel.π (u.natTrans.app j) :=
  cokernel.π_desc _ _ _

/-- **Stacks 0127, the right-exact half**, for a strict morphism of filtered objects: the map
`gr^p I ⟶ gr^p Coker(u)` is a cokernel of `gr^p A ⟶ gr^p I`. -/
private noncomputable def isColimit_cokernelCofork_gradedPiece_cokernelπ
    {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I) [IsStrictHom u] (p : ℤ)
    (w : (gr p).map u ≫ (gr p).map (cokernelπ u) = 0) :
    IsColimit (CokernelCofork.ofπ ((gr p).map (cokernelπ u)) w) :=
  isColimit_cokernelCofork_of_cokernel_π
    (π₁ := cokernel.π (u.natTrans.app (op (p + 1))))
    (π_comp_cokernelObj_diagram_map u _) (cokernel.π_desc _ _ _) (cokernel.π_desc _ _ _) w

/-- **Stacks 0127.** For a strict monomorphism `u : A ⟶ I` of filtered objects the sequence
`0 → gr^p A → gr^p I → gr^p Coker(u) → 0` is short exact: it induces a short exact sequence of
graded pieces in every degree. -/
@[ega "IV 19.6.1" "more general"]
lemma shortExact_gradedPiece_cokernelπ {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I)
    [IsStrictHom u] (p : ℤ)
    (w : (gr p).map u ≫ (gr p).map (cokernelπ u) = 0) :
    (ShortComplex.mk _ _ w).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _
    (isColimit_cokernelCofork_gradedPiece_cokernelπ u p w)
  mono_f := mono_gradedPiece_map u p
  epi_g := Cofork.IsColimit.epi (isColimit_cokernelCofork_gradedPiece_cokernelπ u p w)

/-- Exactness of a short complex is unchanged by composing its second map with a monomorphism. -/
private lemma exact_comp_mono {X Y Z Z' : 𝒜} {f : X ⟶ Y} {g : Y ⟶ Z} {m : Z ⟶ Z'} [Mono m]
    {hfg : f ≫ g = 0} {h' : f ≫ g ≫ m = 0} (h : (ShortComplex.mk f g hfg).Exact) :
    (ShortComplex.mk f (g ≫ m) h').Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk f g hfg) (S₂ := ShortComplex.mk f (g ≫ m) h')
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := m }).1 h

/-- Exactness of a short complex is unchanged by composing its first map with an epimorphism on
the left and its second map with a monomorphism on the right. -/
private lemma exact_epi_comp_comp_mono {X' X Y Z Z' : 𝒜} {e : X' ⟶ X} {f : X ⟶ Y} {g : Y ⟶ Z}
    {m : Z ⟶ Z'} [Epi e] [Mono m] {hfg : f ≫ g = 0} {h' : (e ≫ f) ≫ g ≫ m = 0}
    (h : (ShortComplex.mk f g hfg).Exact) : (ShortComplex.mk (e ≫ f) (g ≫ m) h').Exact := by
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (e ≫ f) (g ≫ m) h')
    (S₂ := ShortComplex.mk f (g ≫ m) (by rw [← Category.assoc, hfg, zero_comp]))
    { τ₁ := e, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }).2 (exact_comp_mono h)

/-- Exactness of a short complex depends only on its two maps. -/
private lemma exact_of_eq {X Y Z : 𝒜} {f f' : X ⟶ Y} {g g' : Y ⟶ Z} {h : f ≫ g = 0}
    {h' : f' ≫ g' = 0} (hf : f = f') (hg : g = g') (H : (ShortComplex.mk f g h).Exact) :
    (ShortComplex.mk f' g' h').Exact := by
  subst hf; subst hg; exact H

/-- The composite `gr^p A ⟶ gr^p I ⟶ gr^p Coker(u)` vanishes. -/
lemma gradedPiece_map_comp_cokernelπ {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I)
    [IsStrictHom u] (p : ℤ) :
    (gr p).map u ≫ (gr p).map (cokernelπ u) = 0 := by
  rw [← cancel_epi (grMapπ (succHom p) A), comp_zero, ← Category.assoc, grMapπ_map,
    Category.assoc, grMapπ_map, ← Category.assoc,
    natTrans_app_comp_cokernelπ_natTrans_app, zero_comp]

/-- **Stacks 0127, the surjectivity half.** The graded pieces of the projection onto the cokernel
of a strict morphism of filtered objects are epimorphisms. -/
private lemma epi_gradedPiece_map_cokernelπ {A I : FilteredObject 𝒜 ℤᵒᵖ} (u : A ⟶ I)
    [IsStrictHom u] (p : ℤ) : Epi ((gr p).map (cokernelπ u)) :=
  Cofork.IsColimit.epi
    (isColimit_cokernelCofork_gradedPiece_cokernelπ u p (gradedPiece_map_comp_cokernelπ u p))

end Cokernel

end CochainComplex.FilteredInjective.Resolution

end FilteredInjectiveResolutionDegreeZero

end
