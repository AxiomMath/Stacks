module

public import StacksFrontier.CategoryTheory.Sites.Stackification.RawLocalEquality

/-! # Local faithfulness and local fullness of the transpose of a 1-morphism over a functor

Let `u : 𝒞 ⥤ 𝒟` be a functor, let `p : 𝒮 ⥤ 𝒞` and `q : 𝒯 ⥤ 𝒟` be fibred categories, let `𝒞` have
nonempty finite limits and let `u` commute with them, and let `F : 𝒮 ⥤ 𝒯` be a functor over `u`
carrying strongly cartesian morphisms to strongly cartesian morphisms. The adjunction of
Stacks 04WI transposes `F` to the 1-morphism

`B(F) : u_p 𝒮 ⥤ 𝒯`, `(V, x, φ : V ⟶ u(p x)) ↦ φ^* F(x)`,

of `CategoryTheory.PullbackAdjunction.leftToRight`. This file reduces the two raw statements of
clause (1) of Stacks 02ZN for `B(F)` — that it identifies only locally equal morphisms, and that
every morphism between its values is locally in its image — to the corresponding two statements
about `F` itself, in which only morphisms of `𝒮` and the chosen pullbacks `φ^* F(x)` occur and no
morphism of the localization `u_p 𝒮` does.

The reduction is the calculus of fractions of Stacks 04WF twice over. A morphism of `u_p 𝒮` is a
fraction `Q(s)⁻¹ ∘ Q(h)` with `s` in the right multiplicative system, so a pair of morphisms
written over one denominator (Categories 04VI) is locally equal as soon as the two numerators are;
and a morphism `(β, e)` of `u_pp 𝒮` whose `𝒮`-component is strongly cartesian factors as an
element of the system followed by the reindexing morphism of Stacks 04WG, hence becomes strongly
cartesian in `u_p 𝒮`. Every morphism of `u_p 𝒮` lying over `β` therefore factors through such a
`(β, e)` up to an isomorphism over an identity, and the local statements need only be tested on
those.

## Main definitions

* `CategoryTheory.PullbackAdjunction.commaHomOf`: the morphism of `u_pp 𝒮` into `Z` with
  prescribed `𝒟`- and `𝒮`-components.
* `CategoryTheory.PullbackAdjunction.baseOfLeftToRightHom`: the morphism of `𝒟` that a morphism
  of `𝒯` between two chosen pullbacks lies over.

## Main results

* `CategoryTheory.PullbackAdjunction.leftToRight_map_Q_map`: `B(F)` on the image of a morphism of
  `u_pp 𝒮` is the morphism of chosen pullbacks that it induces.
* `CategoryTheory.PullbackAdjunction.isStronglyCartesian_Q_commaHomOf`: a morphism of `u_pp 𝒮`
  with strongly cartesian `𝒮`-component becomes strongly cartesian in `u_p 𝒮`.
* `CategoryTheory.PullbackAdjunction.locallyEqual_of_leftToRight_map_eq`: **local faithfulness** —
  two morphisms of `u_p 𝒮` with the same image under `B(F)` are locally equal.
* `CategoryTheory.PullbackAdjunction.exists_covering_leftToRight_map_comp`: **local fullness** —
  every morphism between values of `B(F)` is, along a covering sieve of the base, the image under
  `B(F)` of a morphism of `u_p 𝒮`.
* `CategoryTheory.PullbackAdjunction.exists_equalizing_factorization`,
  `CategoryTheory.PullbackAdjunction.hfaith_of_equalBase` and
  `CategoryTheory.PullbackAdjunction.hcore_of_fibrePair`: the reduction of the
  local-faithfulness hypothesis, first to a pair of morphisms lying over one morphism of `𝒞` and
  then to a pair of morphisms of a single fibre of `𝒮`.

## Implementation notes

The chosen pullback `φ^* F(x)` and the value of `B(F)` at `Q(V, x, φ)` are definitionally equal
but not syntactically so, so a rewrite whose pattern mentions one of them is matched against the
other at `implicit` transparency and fails. The two identities `B(F)(Q(f)) = φ^* F(f)` and
`eqToHom _ = 𝟙` that cross this boundary are therefore applied in term mode.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 04WF](https://stacks.math.columbia.edu/tag/04WF)
* [Stacks Project, Tag 04WG](https://stacks.math.columbia.edu/tag/04WG)
* [Stacks Project, Tag 04WI](https://stacks.math.columbia.edu/tag/04WI)
-/

@[expose] public noncomputable section

namespace CategoryTheory.PullbackAdjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮] {𝒯 : Type u₄} [Category.{v₄} 𝒯]

/-- **Two morphisms of `𝒞` that `φ` equalizes after applying `u` are equalized by a morphism
through which `φ` factors.** The equalizer of the two morphisms exists in `𝒞` and is preserved by
`u`, so `φ` factors through its image.

The hypotheses are taken as explicit arguments rather than as instances: at the localized big fppf
sites the two categories are reached through `AlgebraicGeometry.BigFppfOver`, whose category
instance is not the one that instance search finds for the source of the localized inclusion, so
the instances have to be supplied by hand at the point of use. -/
theorem exists_equalizing_factorization (u : 𝒞 ⥤ 𝒟)
    (heq : Limits.HasLimitsOfShape Limits.WalkingParallelPair 𝒞)
    (hpres : Limits.PreservesLimitsOfShape Limits.WalkingParallelPair u)
    {T T' : 𝒞} (b₁ b₂ : T ⟶ T') {V : 𝒟} (φ : V ⟶ u.obj T)
    (hφ : φ ≫ u.map b₁ = φ ≫ u.map b₂) :
    ∃ (E : 𝒞) (e : E ⟶ T) (φ' : V ⟶ u.obj E), φ' ≫ u.map e = φ ∧ e ≫ b₁ = e ≫ b₂ := by
  have hhas : Limits.HasEqualizer b₁ b₂ := heq.has_limit _
  have hpl : Limits.PreservesLimit (Limits.parallelPair b₁ b₂) u := hpres.preservesLimit
  have hcond : Limits.equalizer.ι b₁ b₂ ≫ b₁ = Limits.equalizer.ι b₁ b₂ ≫ b₂ :=
    Limits.equalizer.condition b₁ b₂
  have hmap := Limits.isLimitForkMapOfIsLimit u hcond (Limits.equalizerIsEqualizer b₁ b₂)
  obtain ⟨l, hlfac⟩ := Limits.Fork.IsLimit.lift' hmap φ hφ
  exact ⟨Limits.equalizer b₁ b₂, Limits.equalizer.ι b₁ b₂, l, hlfac, hcond⟩

variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)

/-- **The morphism of `u_pp 𝒮` into `Z` with prescribed components**: a morphism
`e : x₁ ⟶ Z.right` of `𝒮` and a morphism `β : V₁ ⟶ Z.left` of `𝒟` satisfying the compatibility
condition of `u_pp 𝒮`. -/
def commaHomOf (Z : Comma (𝟭 𝒟) (p ⋙ u)) {x₁ : 𝒮} {V₁ : 𝒟} (e : x₁ ⟶ Z.right)
    (β : V₁ ⟶ Z.left) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
    (hw : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom) :
    (Comma.mk V₁ x₁ φ₁ : Comma (𝟭 𝒟) (p ⋙ u)) ⟶ Z where
  left := β
  right := e
  w := by simpa using hw.symm

/-- The `𝒟`-component of the morphism `commaHomOf p u Z e β φ₁ hw` is `β`. -/
@[simp]
lemma commaHomOf_left (Z : Comma (𝟭 𝒟) (p ⋙ u)) {x₁ : 𝒮} {V₁ : 𝒟} (e : x₁ ⟶ Z.right)
    (β : V₁ ⟶ Z.left) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
    (hw : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom) : (commaHomOf p u Z e β φ₁ hw).left = β := rfl

/-- The `𝒮`-component of the morphism `commaHomOf p u Z e β φ₁ hw` is `e`. -/
@[simp]
lemma commaHomOf_right (Z : Comma (𝟭 𝒟) (p ⋙ u)) {x₁ : 𝒮} {V₁ : 𝒟} (e : x₁ ⟶ Z.right)
    (β : V₁ ⟶ Z.left) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
    (hw : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom) : (commaHomOf p u Z e β φ₁ hw).right = e := rfl

/-- The prescribed morphism factors as a morphism with identity `𝒟`-component followed by the
reindexing morphism of Stacks 04WG. -/
lemma commaHomOf_eq_comp (Z : Comma (𝟭 𝒟) (p ⋙ u)) {x₁ : 𝒮} {V₁ : 𝒟} (e : x₁ ⟶ Z.right)
    (β : V₁ ⟶ Z.left) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
    (hw : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom) :
    commaHomOf p u Z e β φ₁ hw =
      Comma.idBaseHomTo p u e φ₁ (β ≫ Z.hom) hw ≫ Comma.baseChangeHom p u Z β :=
  Comma.hom_ext _ _ (by simp) (by simp)

variable (q : 𝒯 ⥤ 𝒟) [q.IsFibered] (F : 𝒮 ⥤ 𝒯) (hF : F ⋙ q = p ⋙ u)

/-- The base morphism of the morphism of chosen pullbacks induced by a morphism of `u_pp 𝒮`,
read through the identification of the base of a chosen pullback. -/
lemma map_leftToRightHom {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    q.map (leftToRightHom p u q F hF f) =
      eqToHom (leftToRightObj_proj p u q F hF Z) ≫ f.left ≫
        eqToHom (leftToRightObj_proj p u q F hF Z').symm :=
  IsHomLift.fac' q f.left (leftToRightHom p u q F hF f)

/-- Two morphisms of `u_pp 𝒮` inducing the same morphism of chosen pullbacks have the same
`𝒟`-component. -/
lemma left_eq_of_leftToRightHom_eq {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f g : Z ⟶ Z')
    (h : leftToRightHom p u q F hF f = leftToRightHom p u q F hF g) : f.left = g.left := by
  have d := congrArg q.map h
  rw [map_leftToRightHom p u q F hF f, map_leftToRightHom p u q F hF g] at d
  exact (cancel_mono (eqToHom (leftToRightObj_proj p u q F hF Z').symm)).1
    ((cancel_epi (eqToHom (leftToRightObj_proj p u q F hF Z))).1 d)

/-- **The morphism of `𝒟` that a morphism of `𝒯` between two chosen pullbacks lies over.** -/
def baseOfLeftToRightHom {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)}
    (θ : leftToRightObj p u q F hF Z ⟶ leftToRightObj p u q F hF Z') : Z.left ⟶ Z'.left :=
  eqToHom (leftToRightObj_proj p u q F hF Z).symm ≫ q.map θ ≫
    eqToHom (leftToRightObj_proj p u q F hF Z')

/-- A morphism of `𝒯` between two chosen pullbacks lies over the morphism of `𝒟` named by
`CategoryTheory.PullbackAdjunction.baseOfLeftToRightHom`. -/
lemma isHomLift_baseOfLeftToRightHom {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)}
    (θ : leftToRightObj p u q F hF Z ⟶ leftToRightObj p u q F hF Z') :
    q.IsHomLift (baseOfLeftToRightHom p u q F hF θ) θ :=
  IsHomLift.of_fac' q _ θ (leftToRightObj_proj p u q F hF Z)
    (leftToRightObj_proj p u q F hF Z') (by simp [baseOfLeftToRightHom])

/-- **Any strongly cartesian morphism over `φ₁` with target `F(x₁)` may be used in place of the
chosen one.** It differs from the chosen one by an isomorphism over an identity, and that
isomorphism identifies a morphism into `φ^* F(x)` lying over `β` with the induced morphism of
chosen pullbacks. -/
lemma exists_iso_leftToRightMap (Z : Comma (𝟭 𝒟) (p ⋙ u)) {x₁ : 𝒮} {V₁ : 𝒟}
    (e : x₁ ⟶ Z.right) (β : V₁ ⟶ Z.left) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
    (hw : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom)
    {z₁ : 𝒯} {μ₁ : z₁ ⟶ F.obj x₁} (hμ₁ : q.IsStronglyCartesian φ₁ μ₁)
    {ν : z₁ ⟶ leftToRightObj p u q F hF Z} (hν : q.IsHomLift β ν)
    (hfacν : ν ≫ leftToRightMap p u q F hF Z = μ₁ ≫ F.map e) :
    ∃ ι : leftToRightObj p u q F hF (Comma.mk V₁ x₁ φ₁) ⟶ z₁,
      ι ≫ μ₁ = leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁) ∧
        ι ≫ ν = leftToRightHom p u q F hF (commaHomOf p u Z e β φ₁ hw) := by
  have h1 := hμ₁
  have h2 : q.IsStronglyCartesian φ₁ (leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁)) :=
    leftToRightMap_isStronglyCartesian p u q F hF (Comma.mk V₁ x₁ φ₁)
  have hrefl : φ₁ = (Iso.refl V₁).hom ≫ φ₁ := by simp
  set ι := (Functor.IsStronglyCartesian.domainIsoOfBaseIso q hrefl μ₁
    (leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁))).hom with hιdef
  have hfac : ι ≫ μ₁ = leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁) := by
    rw [hιdef]
    exact Functor.IsStronglyCartesian.fac q φ₁ μ₁ hrefl
      (leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁))
  have hι : q.IsHomLift (𝟙 V₁) ι := by
    have h0 : q.IsHomLift (Iso.refl V₁).hom ι := by
      rw [hιdef]
      exact Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift q hrefl μ₁
        (leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁))
    exact h0
  refine ⟨ι, hfac, ?_⟩
  refine leftToRightHom_eq p u q F hF (commaHomOf p u Z e β φ₁ hw) _ ?_ ?_
  · have h3 := hι
    have h4 := hν
    have h5 : q.IsHomLift (𝟙 V₁ ≫ β) (ι ≫ ν) := IsHomLift.comp q (𝟙 V₁) β ι ν
    rwa [Category.id_comp] at h5
  · rw [Category.assoc, hfacν, ← Category.assoc, hfac]
    rfl

variable (hFsc : ∀ {x y : 𝒮} (α : x ⟶ y), p.IsStronglyCartesian (p.map α) α →
    q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))

/-- `B(F)` on the image in `u_p 𝒮` of a morphism of `u_pp 𝒮` is the morphism of chosen pullbacks
that it induces. -/
theorem leftToRight_map_Q_map {Z Z' : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ Z') :
    (leftToRight p u q F hF hFsc).map ((Comma.idBaseStronglyCartesian p u).Q.map f) =
      leftToRightHom p u q F hF f := by
  have h := Functor.congr_hom (leftToRight_fac p u q F hF hFsc) f
  have e₁ : eqToHom (Functor.congr_obj (leftToRight_fac p u q F hF hFsc) Z) =
      𝟙 ((leftToRight p u q F hF hFsc).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z)) :=
    eqToHom_refl _ _
  have e₂ : eqToHom (Functor.congr_obj (leftToRight_fac p u q F hF hFsc) Z').symm =
      𝟙 (leftToRightObj p u q F hF Z') := eqToHom_refl _ _
  refine Eq.trans h ?_
  rw [e₁, e₂]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Every object of `u_p 𝒮` is the image of an object of `u_pp 𝒮`. -/
private lemma exists_Q_obj_eq (B : Comma.pullbackLocalization p u) :
    ∃ Z, (Comma.idBaseStronglyCartesian p u).Q.obj Z = B :=
  ⟨_, (Localization.Construction.objEquiv (Comma.idBaseStronglyCartesian p u)).apply_symm_apply B⟩

/-- The chosen cartesian morphism of a fibred category over `f` is strongly cartesian over
`p.map f`, in the sense of `stronglyCartesianOver`. -/
private lemma stronglyCartesianOver_pullbackMap [p.IsFibered] {a : 𝒮} {R : 𝒞} (f : R ⟶ p.obj a) :
    stronglyCartesianOver p (Functor.IsPreFibered.pullbackMap (rfl : p.obj a = p.obj a) f) := by
  have := Functor.IsPreFibered.pullbackMap.IsCartesian (rfl : p.obj a = p.obj a) f
  dsimp only [stronglyCartesianOver]
  rw [IsHomLift.fac' p f (Functor.IsPreFibered.pullbackMap (rfl : p.obj a = p.obj a) f)]
  exact Functor.IsStronglyCartesian.eqToHom_comp_eqToHom _ _ _ _ inferInstance

/-- `F` carries the chosen cartesian morphism over `f` to a strongly cartesian morphism over
`u.map f`. -/
private lemma isStronglyCartesian_map_pullbackMap [p.IsFibered] {q : 𝒯 ⥤ 𝒟} {F : 𝒮 ⥤ 𝒯}
    (hFsc : ∀ {x y : 𝒮} (α : x ⟶ y), p.IsStronglyCartesian (p.map α) α →
      q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    {a : 𝒮} {R : 𝒞} (f : R ⟶ p.obj a) :
    q.IsStronglyCartesian (u.map f)
      (F.map (Functor.IsPreFibered.pullbackMap (rfl : p.obj a = p.obj a) f)) := by
  have h0 := hFsc _ (stronglyCartesianOver_pullbackMap p f)
  rw [Functor.comp_map, IsHomLift.fac' p f (Functor.IsPreFibered.pullbackMap rfl f)] at h0
  simp only [eqToHom_refl, Category.comp_id, Functor.map_comp, eqToHom_map] at h0
  exact Functor.IsStronglyCartesian.of_eqToHom_comp _ _ _ h0

variable [p.IsFibered] [HasNonemptyFiniteLimits 𝒞]

/-- **A morphism of `u_pp 𝒮` with strongly cartesian `𝒮`-component becomes strongly cartesian in
`u_p 𝒮`**, over its `𝒟`-component: the first factor of
`CategoryTheory.PullbackAdjunction.commaHomOf_eq_comp` is inverted by the localization and the
second is the reindexing morphism of Stacks 04WG. -/
lemma isStronglyCartesian_Q_commaHomOf
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (Z : Comma (𝟭 𝒟) (p ⋙ u)) {x₁ : 𝒮} {V₁ : 𝒟} {e : x₁ ⟶ Z.right}
    (he : stronglyCartesianOver p e) (β : V₁ ⟶ Z.left) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
    (hw : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom) :
    (Comma.pullbackProj p u).IsStronglyCartesian β
      ((Comma.idBaseStronglyCartesian p u).Q.map (commaHomOf p u Z e β φ₁ hw)) := by
  rw [commaHomOf_eq_comp, Functor.map_comp]
  exact isStronglyCartesian_id_comp
    (Comma.isStronglyCartesian_Q_of_mem p u _
      (Comma.idBaseStronglyCartesian_idBaseHomTo p u he φ₁ (β ≫ Z.hom) hw))
    (Comma.isStronglyCartesian_Q_baseChangeHom p u hu Z β)

/-- **Local faithfulness of the transpose.** Suppose that whenever two morphisms of `𝒮` out of
`Z.right` have the same composite with the chosen cartesian morphism `φ^* F(x) ⟶ F(x)`, they agree
after base change along a strongly cartesian morphism through which the structure morphism of `Z`
factors, locally on `Z.left`. Then two morphisms of `u_p 𝒮` with the same image under `B(F)` are
locally equal. -/
theorem locallyEqual_of_leftToRight_map_eq (K : GrothendieckTopology 𝒟)
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (hfaith : ∀ (Z : Comma (𝟭 𝒟) (p ⋙ u)) {y : 𝒮} (α₁ α₂ : Z.right ⟶ y),
      leftToRightMap p u q F hF Z ≫ F.map α₁ = leftToRightMap p u q F hF Z ≫ F.map α₂ →
      ∃ T ∈ K Z.left, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ Z.left⦄, T.arrows β →
        ∃ (x₁ : 𝒮) (e : x₁ ⟶ Z.right) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
          (_ : stronglyCartesianOver p e) (_ : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom),
          e ≫ α₁ = e ≫ α₂)
    {A B : Comma.pullbackLocalization p u} (v v' : A ⟶ B)
    (h : (leftToRight p u q F hF hFsc).map v = (leftToRight p u q F hF hFsc).map v') :
    (Comma.pullbackProj p u).LocallyEqual K v v' := by
  have hrcf := Comma.hasRightCalculusOfFractions_idBaseStronglyCartesian p u hu
  have hfib : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
  obtain ⟨Z', rfl⟩ := exists_Q_obj_eq p u B
  obtain ⟨Z, rfl⟩ := exists_Q_obj_eq p u A
  obtain ⟨Z₀, s, hs, h₁, h₂, e₁, e₂⟩ := Localization.exists_common_denominator
    (Comma.idBaseStronglyCartesian p u).Q (Comma.idBaseStronglyCartesian p u) v v'
  have hsiso : IsIso ((Comma.idBaseStronglyCartesian p u).Q.map s) :=
    Localization.inverts _ (Comma.idBaseStronglyCartesian p u) _ hs
  -- The two numerators have the same image under `B(F)`.
  have hnum : leftToRightHom p u q F hF h₁ = leftToRightHom p u q F hF h₂ := by
    rw [← leftToRight_map_Q_map p u q F hF hFsc, ← leftToRight_map_Q_map p u q F hF hFsc,
      ← e₁, ← e₂, Functor.map_comp, Functor.map_comp, h]
  have hleft : h₁.left = h₂.left := left_eq_of_leftToRightHom_eq p u q F hF h₁ h₂ hnum
  have hfac : leftToRightMap p u q F hF Z₀ ≫ F.map h₁.right =
      leftToRightMap p u q F hF Z₀ ≫ F.map h₂.right := by
    rw [← leftToRightHom_fac p u q F hF h₁, ← leftToRightHom_fac p u q F hF h₂, hnum]
  obtain ⟨T, hT, hspec⟩ := hfaith Z₀ h₁.right h₂.right hfac
  -- Local equality of the two numerators.
  have key : (Comma.pullbackProj p u).LocallyEqual K
      ((Comma.idBaseStronglyCartesian p u).Q.map h₁)
      ((Comma.idBaseStronglyCartesian p u).Q.map h₂) := by
    have hZ₀ : (Comma.pullbackProj p u).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z₀) =
        Z₀.left := Comma.pullbackProj_obj p u Z₀
    refine Functor.LocallyEqual.of_isStronglyCartesian ?_
      (R := Sieve.pullback (eqToHom hZ₀) T) (K.pullback_stable _ hT) ?_
    · rw [Comma.pullbackProj_map, Comma.pullbackProj_map, hleft]
    intro V₁ β hβ w φ hφ
    have hβ' : T.arrows (β ≫ eqToHom hZ₀) := hβ
    obtain ⟨x₁, e, φ₁, he, hwe, heq⟩ := hspec hβ'
    have hcart := isStronglyCartesian_Q_commaHomOf p u hu Z₀ he (β ≫ eqToHom hZ₀) φ₁ hwe
    have hφ' : (Comma.pullbackProj p u).IsStronglyCartesian (β ≫ eqToHom hZ₀) φ :=
      isStronglyCartesian_comp_eqToHom hZ₀ β φ hφ
    have hrefl : β ≫ eqToHom hZ₀ = (Iso.refl V₁).hom ≫ (β ≫ eqToHom hZ₀) := by simp
    have hc := hcart
    have hp := hφ'
    have hδfac : (Functor.IsStronglyCartesian.domainIsoOfBaseIso (Comma.pullbackProj p u) hrefl
          ((Comma.idBaseStronglyCartesian p u).Q.map
            (commaHomOf p u Z₀ e (β ≫ eqToHom hZ₀) φ₁ hwe)) φ).hom ≫
        (Comma.idBaseStronglyCartesian p u).Q.map
          (commaHomOf p u Z₀ e (β ≫ eqToHom hZ₀) φ₁ hwe) = φ :=
      Functor.IsStronglyCartesian.fac (Comma.pullbackProj p u) (β ≫ eqToHom hZ₀) _ hrefl φ
    have hcomma : commaHomOf p u Z₀ e (β ≫ eqToHom hZ₀) φ₁ hwe ≫ h₁ =
        commaHomOf p u Z₀ e (β ≫ eqToHom hZ₀) φ₁ hwe ≫ h₂ := by
      refine Comma.hom_ext _ _ ?_ ?_
      · simpa using congrArg (fun t => (β ≫ eqToHom hZ₀) ≫ t) hleft
      · simpa using heq
    rw [← hδfac, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hcomma]
  -- Transport back along the common denominator.
  have hv := (IsIso.eq_inv_comp _).2 e₁
  have hv' := (IsIso.eq_inv_comp _).2 e₂
  rw [hv, hv']
  exact HomRel.comp_left (r := (Comma.pullbackProj p u).locallyEqualRel K) _ key

/-- **Local fullness of the transpose.** Suppose that every morphism `φ^* F(x) ⟶ F(y)` of `𝒯`
becomes, locally on `Z.left` and after base change along a strongly cartesian morphism through
which the structure morphism of `Z` factors, the one induced by a morphism of `𝒮`. Then every
morphism between values of `B(F)` is, along a covering sieve of the base, the image under `B(F)`
of a morphism of `u_p 𝒮`. -/
theorem exists_covering_leftToRight_map_comp (K : GrothendieckTopology 𝒟)
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (hfull : ∀ (Z : Comma (𝟭 𝒟) (p ⋙ u)) {y : 𝒮}
      (Θ : leftToRightObj p u q F hF Z ⟶ F.obj y),
      ∃ T ∈ K Z.left, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ Z.left⦄, T.arrows β →
        ∃ (x₁ : 𝒮) (e : x₁ ⟶ Z.right) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
          (_ : stronglyCartesianOver p e) (hw : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom) (α : x₁ ⟶ y),
          leftToRightHom p u q F hF (commaHomOf p u Z e β φ₁ hw) ≫ Θ =
            leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁) ≫ F.map α)
    {A B : Comma.pullbackLocalization p u}
    (θ : (leftToRight p u q F hF hFsc).obj A ⟶ (leftToRight p u q F hF hFsc).obj B) :
    ∃ T ∈ K ((Comma.pullbackProj p u).obj A),
      ∀ ⦃w : Comma.pullbackLocalization p u⦄ (ρ : w ⟶ A),
        T.arrows ((Comma.pullbackProj p u).map ρ) →
        ∃ k : w ⟶ B, (leftToRight p u q F hF hFsc).map ρ ≫ θ =
          (leftToRight p u q F hF hFsc).map k := by
  obtain ⟨Z', rfl⟩ := exists_Q_obj_eq p u B
  obtain ⟨Z, rfl⟩ := exists_Q_obj_eq p u A
  have hZ : (Comma.pullbackProj p u).obj ((Comma.idBaseStronglyCartesian p u).Q.obj Z) = Z.left :=
    Comma.pullbackProj_obj p u Z
  set θ₀ : leftToRightObj p u q F hF Z ⟶ leftToRightObj p u q F hF Z' := θ with hθ₀
  obtain ⟨T, hT, hspec⟩ := hfull Z (θ₀ ≫ leftToRightMap p u q F hF Z')
  refine ⟨Sieve.pullback (eqToHom hZ) T, K.pullback_stable _ hT, ?_⟩
  intro w ρ hρ
  set V₁ := (Comma.pullbackProj p u).obj w with hV₁
  set β := (Comma.pullbackProj p u).map ρ ≫ eqToHom hZ with hβ
  have hρ' : T.arrows β := hρ
  obtain ⟨x₁, e, φ₁, he, hwe, α, hΘ⟩ := hspec hρ'
  have hcart := isStronglyCartesian_Q_commaHomOf p u hu Z he β φ₁ hwe
  have hρlift : (Comma.pullbackProj p u).IsHomLift β ρ :=
    IsHomLift.of_fac' (Comma.pullbackProj p u) β ρ rfl hZ (by rw [hβ]; simp)
  have hone : β = 𝟙 V₁ ≫ β := by simp
  have hc := hcart
  have hl := hρlift
  have hεfac : Functor.IsStronglyCartesian.map (Comma.pullbackProj p u) β
        ((Comma.idBaseStronglyCartesian p u).Q.map (commaHomOf p u Z e β φ₁ hwe)) hone ρ ≫
      (Comma.idBaseStronglyCartesian p u).Q.map (commaHomOf p u Z e β φ₁ hwe) = ρ :=
    Functor.IsStronglyCartesian.fac (Comma.pullbackProj p u) β _ hone ρ
  set ε := Functor.IsStronglyCartesian.map (Comma.pullbackProj p u) β
    ((Comma.idBaseStronglyCartesian p u).Q.map (commaHomOf p u Z e β φ₁ hwe)) hone ρ with hε
  -- The `𝒟`-component of the morphism of `u_pp 𝒮` to be built.
  set ψ := baseOfLeftToRightHom p u q F hF θ₀ with hψ
  have hθlift : q.IsHomLift ψ θ₀ := isHomLift_baseOfLeftToRightHom p u q F hF θ₀
  have hk₀lift : q.IsHomLift β (leftToRightHom p u q F hF (commaHomOf p u Z e β φ₁ hwe)) :=
    leftToRightHom_isHomLift p u q F hF (commaHomOf p u Z e β φ₁ hwe)
  have hmlift : q.IsHomLift Z'.hom (leftToRightMap p u q F hF Z') :=
    (leftToRightMap_isStronglyCartesian p u q F hF Z').toIsHomLift
  have hm₁lift : q.IsHomLift φ₁ (leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁)) :=
    (leftToRightMap_isStronglyCartesian p u q F hF (Comma.mk V₁ x₁ φ₁)).toIsHomLift
  have hαlift := isHomLift_map_of_comp p u q F hF α
  -- Its compatibility condition, read off from the two base morphisms of `hΘ`.
  have hwα : φ₁ ≫ (p ⋙ u).map α = β ≫ ψ ≫ Z'.hom := by
    have hθm : q.IsHomLift (ψ ≫ Z'.hom) (θ₀ ≫ leftToRightMap p u q F hF Z') :=
      IsHomLift.comp q ψ Z'.hom θ₀ (leftToRightMap p u q F hF Z')
    have hL : q.IsHomLift (β ≫ ψ ≫ Z'.hom)
        (leftToRightHom p u q F hF (commaHomOf p u Z e β φ₁ hwe) ≫
          θ₀ ≫ leftToRightMap p u q F hF Z') :=
      IsHomLift.comp q β (ψ ≫ Z'.hom) _ _
    have hR : q.IsHomLift (φ₁ ≫ (p ⋙ u).map α)
        (leftToRightMap p u q F hF (Comma.mk V₁ x₁ φ₁) ≫ F.map α) :=
      IsHomLift.comp q φ₁ ((p ⋙ u).map α) _ _
    exact Functor.base_eq_of_isHomLift_of_eq q _ _ _ _ hΘ.symm hR hL
  have hwα' : φ₁ ≫ (p ⋙ u).map α = (β ≫ ψ) ≫ Z'.hom :=
    hwα.trans (Category.assoc β ψ Z'.hom).symm
  -- `B(F)` of the new morphism is the composite.
  have hkey : leftToRightHom p u q F hF (commaHomOf p u Z e β φ₁ hwe) ≫ θ₀ =
      leftToRightHom p u q F hF (commaHomOf p u Z' α (β ≫ ψ) φ₁ hwα') := by
    refine leftToRightHom_eq p u q F hF (commaHomOf p u Z' α (β ≫ ψ) φ₁ hwα') _ ?_ ?_
    · exact IsHomLift.comp q β ψ _ _
    · exact (Category.assoc _ _ _).trans hΘ
  refine ⟨ε ≫ (Comma.idBaseStronglyCartesian p u).Q.map
    (commaHomOf p u Z' α (β ≫ ψ) φ₁ hwα'), ?_⟩
  refine Eq.trans ?_ (Functor.map_comp (leftToRight p u q F hF hFsc) ε
    ((Comma.idBaseStronglyCartesian p u).Q.map (commaHomOf p u Z' α (β ≫ ψ) φ₁ hwα'))).symm
  rw [← hεfac, Functor.map_comp]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun z => (leftToRight p u q F hF hFsc).map ε ≫ z) ?_
  rw [leftToRight_map_Q_map p u q F hF hFsc, leftToRight_map_Q_map p u q F hF hFsc]
  exact hkey

include hFsc in
omit [HasNonemptyFiniteLimits 𝒞] in
/-- **The hypothesis of local faithfulness, reduced to a pair of morphisms over one morphism of
the base.** Two morphisms of `𝒮` whose composites with the chosen cartesian morphism
`φ^* F(x) ⟶ F(x)` agree lie over two morphisms of `𝒞` equalized by `φ`, hence agree over one
morphism of `𝒞` after base change along the equalizer, through whose image `φ` factors. The
restricted cartesian morphism is again strongly cartesian, and the restriction of
`φ^* F(x) ⟶ F(x)` along it is strongly cartesian over the factoring morphism.

This is the shape in which the local-faithfulness hypothesis of
`CategoryTheory.PullbackAdjunction.locallyEqual_of_leftToRight_map_eq` is supplied: it quantifies
over a pair of morphisms lying over *one* morphism of `𝒞`, which is what lets both their source
and their target be presented over a single test object. -/
theorem hfaith_of_equalBase (K : GrothendieckTopology 𝒟)
    (heq : Limits.HasLimitsOfShape Limits.WalkingParallelPair 𝒞)
    (hpres : Limits.PreservesLimitsOfShape Limits.WalkingParallelPair u)
    (hcore : ∀ (x₀ y₀ : 𝒮) (τ₁ τ₂ : x₀ ⟶ y₀) (_ : p.map τ₁ = p.map τ₂) (V : 𝒟)
      (φ : V ⟶ u.obj (p.obj x₀)) (z : 𝒯) (μ : z ⟶ F.obj x₀)
      (_ : q.IsStronglyCartesian φ μ), μ ≫ F.map τ₁ = μ ≫ F.map τ₂ →
      ∃ T ∈ K V, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        ∃ (x₁ : 𝒮) (e : x₁ ⟶ x₀) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
          (_ : stronglyCartesianOver p e) (_ : φ₁ ≫ (p ⋙ u).map e = β ≫ φ),
          e ≫ τ₁ = e ≫ τ₂)
    (Z : Comma (𝟭 𝒟) (p ⋙ u)) {y : 𝒮} (α₁ α₂ : Z.right ⟶ y)
    (hα : leftToRightMap p u q F hF Z ≫ F.map α₁ = leftToRightMap p u q F hF Z ≫ F.map α₂) :
    ∃ T ∈ K Z.left, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ Z.left⦄, T.arrows β →
      ∃ (x₁ : 𝒮) (e : x₁ ⟶ Z.right) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
        (_ : stronglyCartesianOver p e) (_ : φ₁ ≫ (p ⋙ u).map e = β ≫ Z.hom),
        e ≫ α₁ = e ≫ α₂ := by
  have hmcart : q.IsStronglyCartesian Z.hom (leftToRightMap p u q F hF Z) :=
    leftToRightMap_isStronglyCartesian p u q F hF Z
  have hmlift : q.IsHomLift Z.hom (leftToRightMap p u q F hF Z) := hmcart.toIsHomLift
  have hα₁lift := isHomLift_map_of_comp p u q F hF α₁
  have hα₂lift := isHomLift_map_of_comp p u q F hF α₂
  have hL : q.IsHomLift (Z.hom ≫ (p ⋙ u).map α₁)
      (leftToRightMap p u q F hF Z ≫ F.map α₁) :=
    IsHomLift.comp q Z.hom ((p ⋙ u).map α₁) _ _
  have hR : q.IsHomLift (Z.hom ≫ (p ⋙ u).map α₂)
      (leftToRightMap p u q F hF Z ≫ F.map α₂) :=
    IsHomLift.comp q Z.hom ((p ⋙ u).map α₂) _ _
  have hbase : Z.hom ≫ u.map (p.map α₁) = Z.hom ≫ u.map (p.map α₂) :=
    Functor.base_eq_of_isHomLift_of_eq q _ _ _ _ hα hL hR
  obtain ⟨E, e₀, φE, hφE, he₀⟩ := exists_equalizing_factorization u heq hpres
    (p.map α₁) (p.map α₂) Z.hom hbase
  have hcartOver := stronglyCartesianOver_pullbackMap p e₀
  have he₁ : p.map (Functor.IsPreFibered.pullbackMap rfl e₀) =
      eqToHom (Functor.IsPreFibered.pullbackObj_proj rfl e₀) ≫ e₀ ≫ eqToHom rfl :=
    IsHomLift.fac' p e₀ (Functor.IsPreFibered.pullbackMap rfl e₀)
  have hFcart := isStronglyCartesian_map_pullbackMap p u hFsc e₀
  have hone : Z.hom = φE ≫ u.map e₀ := hφE.symm
  have hc1 := hFcart
  have hc2 := hmcart
  have hc3 := hmlift
  set μE := Functor.IsStronglyCartesian.map q (u.map e₀)
    (F.map (Functor.IsPreFibered.pullbackMap rfl e₀)) hone (leftToRightMap p u q F hF Z)
    with hμEdef
  have hμEfac : μE ≫ F.map (Functor.IsPreFibered.pullbackMap rfl e₀) =
      leftToRightMap p u q F hF Z := by
    rw [hμEdef]
    exact Functor.IsStronglyCartesian.fac q (u.map e₀) _ hone (leftToRightMap p u q F hF Z)
  have hμElift : q.IsHomLift φE μE := by
    rw [hμEdef]
    exact Functor.IsStronglyCartesian.map_isHomLift q (u.map e₀) _ hone
      (leftToRightMap p u q F hF Z)
  have hcomp : q.IsStronglyCartesian (φE ≫ u.map e₀)
      (μE ≫ F.map (Functor.IsPreFibered.pullbackMap rfl e₀)) := by
    rw [hμEfac, ← hone]
    exact hmcart
  have hc4 := hμElift
  have hc5 := hcomp
  have hμEcart : q.IsStronglyCartesian φE μE :=
    Functor.IsStronglyCartesian.of_comp (p := q) (f := φE) (g := u.map e₀) (φ := μE)
      (ψ := F.map (Functor.IsPreFibered.pullbackMap rfl e₀))
  -- the two restricted morphisms lie over one morphism of `𝒞`
  have hτ : p.map (Functor.IsPreFibered.pullbackMap rfl e₀ ≫ α₁) =
      p.map (Functor.IsPreFibered.pullbackMap rfl e₀ ≫ α₂) := by
    rw [p.map_comp, p.map_comp, he₁]
    simp only [eqToHom_refl, Category.comp_id, Category.assoc]
    exact congrArg (fun t => eqToHom (Functor.IsPreFibered.pullbackObj_proj rfl e₀) ≫ t) he₀
  have hhyp : μE ≫ F.map (Functor.IsPreFibered.pullbackMap rfl e₀ ≫ α₁) =
      μE ≫ F.map (Functor.IsPreFibered.pullbackMap rfl e₀ ≫ α₂) := by
    rw [F.map_comp, F.map_comp, ← Category.assoc, ← Category.assoc, hμEfac]
    exact hα
  have hE : p.obj (Functor.IsPreFibered.pullbackObj rfl e₀) = E :=
    Functor.IsPreFibered.pullbackObj_proj rfl e₀
  have hμEcart' : q.IsStronglyCartesian (φE ≫ eqToHom (congrArg u.obj hE).symm) μE :=
    isStronglyCartesian_comp_eqToHom (congrArg u.obj hE).symm φE μE hμEcart
  obtain ⟨T, hT, hspec⟩ := hcore _ y _ _ hτ Z.left
    (φE ≫ eqToHom (congrArg u.obj hE).symm) _ μE hμEcart' hhyp
  refine ⟨T, hT, ?_⟩
  intro V₁ β hβ
  obtain ⟨x₁, e, φ₁, he, hw, heq⟩ := hspec hβ
  refine ⟨x₁, e ≫ Functor.IsPreFibered.pullbackMap rfl e₀, φ₁,
    stronglyCartesianOver_comp p e _ he hcartOver, ?_, ?_⟩
  · rw [Functor.comp_map, p.map_comp, u.map_comp, ← Category.assoc]
    rw [show φ₁ ≫ u.map (p.map e) = β ≫ φE ≫ eqToHom (congrArg u.obj hE).symm from hw]
    rw [he₁]
    simp [eqToHom_map, hφE]
  · exact (Category.assoc _ _ _).trans (heq.trans (Category.assoc _ _ _).symm)

include hF hFsc in
omit [q.IsFibered] [HasNonemptyFiniteLimits 𝒞] in
/-- **The hypothesis of local faithfulness, reduced to a vertical pair in a fibre.** Two morphisms
of `𝒮` lying over one morphism of `𝒞` factor through the chosen cartesian lift of that morphism as
vertical morphisms, which are morphisms of a fibre; the composites with the chosen cartesian lift
of `φ^* F(x) ⟶ F(x)` agree there because the image of that lift under `F` is strongly cartesian
and cancels.

Together with `CategoryTheory.PullbackAdjunction.hfaith_of_equalBase` this reduces the
local-faithfulness hypothesis of
`CategoryTheory.PullbackAdjunction.locallyEqual_of_leftToRight_map_eq` to a statement about two
morphisms of a single fibre of `𝒮` and the chosen restriction maps between the chosen pullbacks —
the form in which a presentation of the two objects of that fibre by points can be used. -/
theorem hcore_of_fibrePair (K : GrothendieckTopology 𝒟)
    (hfib : ∀ (U : 𝒞) (A Bo : p.Fiber U) (n₁ n₂ : A ⟶ Bo) (V : 𝒟) (φ : V ⟶ u.obj U) (z : 𝒯)
      (μ : z ⟶ F.obj A.1) (_ : q.IsStronglyCartesian φ μ),
      μ ≫ F.map (Functor.Fiber.fiberInclusion.map n₁) =
        μ ≫ F.map (Functor.Fiber.fiberInclusion.map n₂) →
      ∃ T ∈ K V, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        ∃ (W : 𝒞) (d : W ⟶ U) (φ₁ : V₁ ⟶ u.obj W), φ₁ ≫ u.map d = β ≫ φ ∧
          Functor.pullbackFiberHom n₁ d = Functor.pullbackFiberHom n₂ d)
    (x₀ y₀ : 𝒮) (τ₁ τ₂ : x₀ ⟶ y₀) (hτ : p.map τ₁ = p.map τ₂) (V : 𝒟)
    (φ : V ⟶ u.obj (p.obj x₀)) (z : 𝒯) (μ : z ⟶ F.obj x₀)
    (hμ : q.IsStronglyCartesian φ μ) (hhyp : μ ≫ F.map τ₁ = μ ≫ F.map τ₂) :
    ∃ T ∈ K V, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
      ∃ (x₁ : 𝒮) (e : x₁ ⟶ x₀) (φ₁ : V₁ ⟶ u.obj (p.obj x₁))
        (_ : stronglyCartesianOver p e) (_ : φ₁ ≫ (p ⋙ u).map e = β ≫ φ),
        e ≫ τ₁ = e ≫ τ₂ := by
  have hlam : p.IsStronglyCartesian (p.map τ₁)
      (Functor.IsPreFibered.pullbackMap (rfl : p.obj y₀ = p.obj y₀) (p.map τ₁)) := by
    have := Functor.IsPreFibered.pullbackMap.IsCartesian (rfl : p.obj y₀ = p.obj y₀) (p.map τ₁)
    infer_instance
  have hone : p.map τ₁ = 𝟙 (p.obj x₀) ≫ p.map τ₁ := by simp
  have ht₁ : p.IsHomLift (p.map τ₁) τ₁ := Functor.IsHomLift.map τ₁
  have ht₂ : p.IsHomLift (p.map τ₁) τ₂ := by rw [hτ]; exact Functor.IsHomLift.map τ₂
  have hl := hlam
  have h1 := ht₁
  have h2 := ht₂
  set σ₁ := Functor.IsStronglyCartesian.map p (p.map τ₁)
    (Functor.IsPreFibered.pullbackMap rfl (p.map τ₁)) hone τ₁ with hσ₁
  set σ₂ := Functor.IsStronglyCartesian.map p (p.map τ₁)
    (Functor.IsPreFibered.pullbackMap rfl (p.map τ₁)) hone τ₂ with hσ₂
  have hσ₁fac : σ₁ ≫ Functor.IsPreFibered.pullbackMap rfl (p.map τ₁) = τ₁ := by
    rw [hσ₁]; exact Functor.IsStronglyCartesian.fac p (p.map τ₁) _ hone τ₁
  have hσ₂fac : σ₂ ≫ Functor.IsPreFibered.pullbackMap rfl (p.map τ₁) = τ₂ := by
    rw [hσ₂]; exact Functor.IsStronglyCartesian.fac p (p.map τ₁) _ hone τ₂
  have hσ₁lift : p.IsHomLift (𝟙 (p.obj x₀)) σ₁ := by
    rw [hσ₁]; exact Functor.IsStronglyCartesian.map_isHomLift p (p.map τ₁) _ hone τ₁
  have hσ₂lift : p.IsHomLift (𝟙 (p.obj x₀)) σ₂ := by
    rw [hσ₂]; exact Functor.IsStronglyCartesian.map_isHomLift p (p.map τ₁) _ hone τ₂
  have hpσ : p.map σ₁ = p.map σ₂ :=
    (IsHomLift.fac' p (𝟙 (p.obj x₀)) σ₁).trans (IsHomLift.fac' p (𝟙 (p.obj x₀)) σ₂).symm
  -- the two restricted morphisms agree after the chosen cartesian lift is cancelled
  have hFlam := isStronglyCartesian_map_pullbackMap p u hFsc (p.map τ₁)
  have hμl := hμ.toIsHomLift
  have hvertF : ∀ (σ : x₀ ⟶ Functor.IsPreFibered.pullbackObj rfl (p.map τ₁)),
      p.IsHomLift (𝟙 (p.obj x₀)) σ → q.IsHomLift φ (μ ≫ F.map σ) := by
    intro σ hσ
    have hs := hσ
    have hFσ := isHomLift_map_of_comp p u q F hF σ
    have hps : (p ⋙ u).map σ =
        eqToHom (congrArg u.obj (IsHomLift.codomain_eq p (𝟙 (p.obj x₀)) σ).symm) := by
      rw [Functor.comp_map, IsHomLift.fac' p (𝟙 (p.obj x₀)) σ]
      simp [eqToHom_map]
    have hFσ' : q.IsHomLift
        (eqToHom (congrArg u.obj (IsHomLift.codomain_eq p (𝟙 (p.obj x₀)) σ).symm))
        (F.map σ) := by rw [← hps]; exact hFσ
    have hx := hFσ'
    refine IsHomLift.of_fac' q φ (μ ≫ F.map σ) (IsHomLift.domain_eq q φ μ)
      ((Functor.congr_obj hF (Functor.IsPreFibered.pullbackObj rfl (p.map τ₁))).trans
        (congrArg u.obj (IsHomLift.codomain_eq p (𝟙 (p.obj x₀)) σ))) ?_
    rw [q.map_comp, IsHomLift.fac' q φ μ,
      IsHomLift.fac' q (eqToHom (congrArg u.obj
        (IsHomLift.codomain_eq p (𝟙 (p.obj x₀)) σ).symm)) (F.map σ)]
    simp
  have hb1 : q.IsHomLift φ (μ ≫ F.map σ₁) := hvertF σ₁ hσ₁lift
  have hb2 : q.IsHomLift φ (μ ≫ F.map σ₂) := hvertF σ₂ hσ₂lift
  have hc := hFlam
  have hyp' : μ ≫ F.map σ₁ = μ ≫ F.map σ₂ := by
    refine Functor.IsStronglyCartesian.ext q (u.map (p.map τ₁))
      (F.map (Functor.IsPreFibered.pullbackMap rfl (p.map τ₁))) φ ?_
    rw [Category.assoc, Category.assoc, ← F.map_comp, ← F.map_comp, hσ₁fac, hσ₂fac]
    exact hhyp
  -- read the two vertical morphisms as morphisms of the fibre over `p x₀`
  have hAx : p.obj x₀ = p.obj x₀ := rfl
  obtain ⟨T, hT, hspec⟩ := hfib (p.obj x₀) (Functor.Fiber.mk hAx)
    (Functor.pullbackFiber p (Functor.Fiber.mk rfl) (p.map τ₁))
    (Functor.Fiber.homMk p (p.obj x₀) σ₁) (Functor.Fiber.homMk p (p.obj x₀) σ₂)
    V φ z μ hμ hyp'
  refine ⟨T, hT, ?_⟩
  intro V₁ β hβ
  obtain ⟨W, d, φ₁, hcompat, hpbh⟩ := hspec hβ
  have hed : p.map (Functor.IsPreFibered.pullbackMap hAx d) =
      eqToHom (Functor.IsPreFibered.pullbackObj_proj hAx d) ≫ d ≫ eqToHom rfl :=
    IsHomLift.fac' p d (Functor.IsPreFibered.pullbackMap hAx d)
  refine ⟨Functor.IsPreFibered.pullbackObj hAx d, Functor.IsPreFibered.pullbackMap hAx d,
    φ₁ ≫ eqToHom (congrArg u.obj (Functor.IsPreFibered.pullbackObj_proj hAx d)).symm, ?_, ?_, ?_⟩
  · exact stronglyCartesianOver_pullbackMap p d
  · rw [Functor.comp_map, hed]
    simp only [eqToHom_refl, Category.comp_id, Functor.map_comp, eqToHom_map,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc]
    exact hcompat
  · have hkey : Functor.IsPreFibered.pullbackMap hAx d ≫ σ₁ =
        Functor.IsPreFibered.pullbackMap hAx d ≫ σ₂ :=
      (Functor.pullbackFiberHom_fac (Functor.Fiber.homMk p (p.obj x₀) σ₁) d).symm.trans
        ((congrArg (fun t => Functor.Fiber.fiberInclusion.map t ≫
            Functor.IsPreFibered.pullbackMap
              (Functor.pullbackFiber p (Functor.Fiber.mk rfl) (p.map τ₁)).2 d) hpbh).trans
          (Functor.pullbackFiberHom_fac (Functor.Fiber.homMk p (p.obj x₀) σ₂) d))
    rw [← hσ₁fac, ← hσ₂fac]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ Functor.IsPreFibered.pullbackMap rfl (p.map τ₁)) hkey).trans
        (Category.assoc _ _ _))

end CategoryTheory.PullbackAdjunction

end
