module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Limits.FintypeCat
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Point.OfPreservesFiniteLimits
public import StacksFrontier.CategoryTheory.Sites.Point.StalkFunctor

/-!
# Weakly left exact functors to sets need not be points

Stacks Remark 00YD: let `C` be a site with a final object `X` and fibre products, and let
`u : C ⥤ Set` be a functor such that

1. `u(X) = {*}` is a singleton,
2. for every pair `U → W ← V` the map `u(U ×_W V) → u(U) ×_{u(W)} u(V)` is surjective,
3. for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective.

Then in general `u` is not a point of `C`.

The example given in the source does not satisfy (2) (see
`StacksFrontier/CategoryTheory/Sites/Point/NonExactStalkCounterexample.lean` and `errata.md`).
Here is a correct example. The site is the skeleton of the category of finite sets, with the
trivial topology `⊥` (only the maximal sieve covers, so every presheaf is a sheaf), and `u`
sends a finite set `S` to the set of nonempty subsets of `S`, a map acting by direct image.

* (1) holds since a one-point set has exactly one nonempty subset.
* (2) holds since for nonempty `A ⊆ U`, `B ⊆ V` with `f(A) = g(B)` the set
  `{(a, b) ∈ U ×_W V | a ∈ A, b ∈ B}` projects onto `A` and onto `B`.
* (3) is automatic for the trivial topology.

The comparison map in (2) is not injective: for `U = V = {0, 1}` over the point, the
diagonal and the whole of `U × U` are two subsets with the same two projections. Hence `u`
does not commute with fibre products, and so `u` is not a point: there is no point of the
site (Mathlib's `GrothendieckTopology.Point`, Stacks 00Y5) with fiber functor `u`, and the
stalk functor `Sh(C) ⥤ Set`, `F ↦ F_p = colim_{(U, x)} F(U)`, is not left exact, since by
Stacks 00Y6 its composite with the Yoneda embedding is `u`.

## Main results

* `nonemptySubsets_pullbackComparison_surjective` and
  `nonemptySubsets_pullbackComparison_not_injective`: the nonempty-subsets functor on sets
  satisfies (2), and its comparison maps are not injective.
* `exists_site_weakly_left_exact_not_point`: Stacks Remark 00YD.
-/

@[expose] public section

namespace CategoryTheory.WeakPullbacksNotPoint

open Limits Opposite PresheafPushforwardStalkAdjunction

universe w

/-! ## The nonempty-subsets functor on sets -/

/-- The set of nonempty subsets of a set `X`. -/
abbrev NonemptySubsets (X : Type w) : Type w := {A : Set X // A.Nonempty}

/-- The direct image `f(A)` of a nonempty subset `A`, a nonempty subset. -/
def NonemptySubsets.map {X Y : Type w} (f : X → Y) (A : NonemptySubsets X) :
    NonemptySubsets Y :=
  ⟨f '' A.1, A.2.image f⟩

/-- The covariant nonempty-subsets functor `Set ⥤ Set`: a set `X` goes to the set of its
nonempty subsets, and a map `f` acts by direct image. -/
@[implicit_reducible]
def nonemptySubsets : Type w ⥤ Type w where
  obj := NonemptySubsets
  map f := TypeCat.ofHom (NonemptySubsets.map f)
  map_id X := by
    ext A
    simp [NonemptySubsets.map]
  map_comp f g := by
    ext A
    simp [NonemptySubsets.map, Set.image_image]

@[simp]
lemma nonemptySubsets_map_apply_coe {X Y : Type w} (f : X ⟶ Y) (A : nonemptySubsets.obj X) :
    (nonemptySubsets.map f A).1 = f '' A.1 :=
  rfl

/-- The point of the pullback `X ×_Z Y` of sets with coordinates `x` and `y`. -/
noncomputable def pullbackMk {X Y Z : Type w} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y)
    (h : f x = g y) : pullback f g :=
  (Types.pullbackIsoPullback f g).inv ⟨(x, y), h⟩

@[simp]
lemma pullbackMk_fst {X Y Z : Type w} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y)
    (h : f x = g y) : pullback.fst f g (pullbackMk f g x y h) = x :=
  Types.pullbackIsoPullback_inv_fst_apply f g ⟨(x, y), h⟩

@[simp]
lemma pullbackMk_snd {X Y Z : Type w} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) (y : Y)
    (h : f x = g y) : pullback.snd f g (pullbackMk f g x y h) = y :=
  Types.pullbackIsoPullback_inv_snd_apply f g ⟨(x, y), h⟩

/-- Two points of a pullback of sets with the same two coordinates are equal. -/
lemma pullback_ext {X Y Z : Type w} (f : X ⟶ Z) (g : Y ⟶ Z) {a b : pullback f g}
    (h₁ : pullback.fst f g a = pullback.fst f g b)
    (h₂ : pullback.snd f g a = pullback.snd f g b) : a = b := by
  apply (mono_iff_injective (Types.pullbackIsoPullback f g).hom).1 inferInstance
  apply Subtype.ext
  apply Prod.ext
  · rw [Types.pullbackIsoPullback_hom_fst, Types.pullbackIsoPullback_hom_fst, h₁]
  · rw [Types.pullbackIsoPullback_hom_snd, Types.pullbackIsoPullback_hom_snd, h₂]

/-- The comparison map of `nonemptySubsets` sends a nonempty subset of `X ×_Z Y` to the pair of
its two projections. -/
lemma nonemptySubsets_pullbackComparison_eq_iff {X Y Z : Type w} (f : X ⟶ Z) (g : Y ⟶ Z)
    (C C' : nonemptySubsets.obj (pullback f g)) :
    pullbackComparison nonemptySubsets f g C = pullbackComparison nonemptySubsets f g C' ↔
      pullback.fst f g '' C.1 = pullback.fst f g '' C'.1 ∧
        pullback.snd f g '' C.1 = pullback.snd f g '' C'.1 := by
  constructor
  · intro h
    have e₁ := ConcreteCategory.congr_arg (pullback.fst (nonemptySubsets.map f)
      (nonemptySubsets.map g)) h
    have e₂ := ConcreteCategory.congr_arg (pullback.snd (nonemptySubsets.map f)
      (nonemptySubsets.map g)) h
    rw [← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.fst _ _),
      ← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.fst _ _),
      pullbackComparison_comp_fst] at e₁
    rw [← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.snd _ _),
      ← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.snd _ _),
      pullbackComparison_comp_snd] at e₂
    exact ⟨congrArg Subtype.val e₁, congrArg Subtype.val e₂⟩
  · rintro ⟨h₁, h₂⟩
    apply pullback_ext
    · rw [← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.fst _ _),
        ← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.fst _ _),
        pullbackComparison_comp_fst]
      exact Subtype.ext h₁
    · rw [← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.snd _ _),
        ← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.snd _ _),
        pullbackComparison_comp_snd]
      exact Subtype.ext h₂

/-- **Condition (2) for `nonemptySubsets`.** For maps of sets `f : X → Z`, `g : Y → Z`, every
pair of nonempty subsets `A ⊆ X`, `B ⊆ Y` with `f(A) = g(B)` is the pair of projections of a
nonempty subset of `X ×_Z Y`, namely of the set of its points lying over `A × B`. -/
theorem nonemptySubsets_pullbackComparison_surjective {X Y Z : Type w} (f : X ⟶ Z)
    (g : Y ⟶ Z) : Function.Surjective (pullbackComparison nonemptySubsets f g) := by
  intro q
  set A : NonemptySubsets X := pullback.fst (nonemptySubsets.map f) (nonemptySubsets.map g) q
  set B : NonemptySubsets Y := pullback.snd (nonemptySubsets.map f) (nonemptySubsets.map g) q
  have hAB : f '' A.1 = g '' B.1 := by
    simpa using congrArg Subtype.val
      (ConcreteCategory.congr_hom (pullback.condition (f := nonemptySubsets.map f)
        (g := nonemptySubsets.map g)) q)
  -- every `a ∈ A` has a partner `b ∈ B` over the same point of `Z`, and conversely
  have hA : ∀ a ∈ A.1, ∃ b ∈ B.1, f a = g b := fun a ha => by
    obtain ⟨b, hb, e⟩ : f a ∈ g '' B.1 := hAB ▸ Set.mem_image_of_mem f ha
    exact ⟨b, hb, e.symm⟩
  have hB : ∀ b ∈ B.1, ∃ a ∈ A.1, f a = g b := fun b hb => by
    obtain ⟨a, ha, e⟩ : g b ∈ f '' A.1 := hAB ▸ Set.mem_image_of_mem g hb
    exact ⟨a, ha, e⟩
  let S : Set (pullback f g) := {p | pullback.fst f g p ∈ A.1 ∧ pullback.snd f g p ∈ B.1}
  obtain ⟨a₀, ha₀⟩ := A.2
  obtain ⟨b₀, hb₀, e₀⟩ := hA a₀ ha₀
  have hS : S.Nonempty := ⟨pullbackMk f g a₀ b₀ e₀, by simpa [S] using ⟨ha₀, hb₀⟩⟩
  refine ⟨(⟨S, hS⟩ : NonemptySubsets (pullback f g)), ?_⟩
  apply pullback_ext
  · rw [← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.fst _ _),
      pullbackComparison_comp_fst]
    refine Subtype.ext (Set.Subset.antisymm ?_ fun a ha => ?_)
    · rintro _ ⟨p, hp, rfl⟩
      exact hp.1
    · obtain ⟨b, hb, e⟩ := hA a ha
      exact ⟨pullbackMk f g a b e, by simpa [S] using ⟨ha, hb⟩, by simp⟩
  · rw [← types_comp_apply (pullbackComparison nonemptySubsets f g) (pullback.snd _ _),
      pullbackComparison_comp_snd]
    refine Subtype.ext (Set.Subset.antisymm ?_ fun b hb => ?_)
    · rintro _ ⟨p, hp, rfl⟩
      exact hp.2
    · obtain ⟨a, ha, e⟩ := hB b hb
      exact ⟨pullbackMk f g a b e, by simpa [S] using ⟨ha, hb⟩, by simp⟩

/-- The comparison maps of `nonemptySubsets` are not injective: if `x ≠ y` have the same image
under `f`, then the diagonal of `{x, y}` and the whole of `{x, y} ×_Z {x, y}` are distinct
nonempty subsets of `X ×_Z X` with the same two projections `{x, y}`. -/
theorem nonemptySubsets_pullbackComparison_not_injective {X Z : Type w} (f : X ⟶ Z)
    {x y : X} (hxy : x ≠ y) (hf : f x = f y) :
    ¬ Function.Injective (pullbackComparison nonemptySubsets f f) := by
  intro hinj
  let T : Set X := {x, y}
  let Sfull : Set (pullback f f) := {p | pullback.fst f f p ∈ T ∧ pullback.snd f f p ∈ T}
  let Sdiag : Set (pullback f f) := {p | pullback.fst f f p ∈ T ∧
    pullback.fst f f p = pullback.snd f f p}
  have hx : pullbackMk f f x x rfl ∈ Sdiag := by simp [Sdiag, T]
  have hy : pullbackMk f f y y rfl ∈ Sdiag := by simp [Sdiag, T]
  have hfull : pullback.fst f f '' Sfull = T ∧ pullback.snd f f '' Sfull = T := by
    refine ⟨Set.Subset.antisymm (by rintro _ ⟨p, hp, rfl⟩; exact hp.1) ?_,
      Set.Subset.antisymm (by rintro _ ⟨p, hp, rfl⟩; exact hp.2) ?_⟩
    · rintro z (rfl | rfl)
      · exact ⟨pullbackMk f f z z rfl, by simp [Sfull, T], by simp⟩
      · exact ⟨pullbackMk f f z z rfl, by simp [Sfull, T], by simp⟩
    · rintro z (rfl | rfl)
      · exact ⟨pullbackMk f f z z rfl, by simp [Sfull, T], by simp⟩
      · exact ⟨pullbackMk f f z z rfl, by simp [Sfull, T], by simp⟩
  have hdiag : pullback.fst f f '' Sdiag = T ∧ pullback.snd f f '' Sdiag = T := by
    refine ⟨Set.Subset.antisymm (by rintro _ ⟨p, hp, rfl⟩; exact hp.1) ?_,
      Set.Subset.antisymm (by rintro _ ⟨p, hp, rfl⟩; exact hp.2 ▸ hp.1) ?_⟩
    · rintro z (rfl | rfl)
      · exact ⟨_, hx, by simp⟩
      · exact ⟨_, hy, by simp⟩
    · rintro z (rfl | rfl)
      · exact ⟨_, hx, by simp⟩
      · exact ⟨_, hy, by simp⟩
  have h := hinj (a₁ := ⟨Sfull, pullbackMk f f x x rfl, by simp [Sfull, T]⟩) (a₂ := ⟨Sdiag, _, hx⟩)
    ((nonemptySubsets_pullbackComparison_eq_iff f f _ _).2
      ⟨hfull.1.trans hdiag.1.symm, hfull.2.trans hdiag.2.symm⟩)
  have h' : Sfull = Sdiag := congrArg Subtype.val h
  have hmem : pullbackMk f f x y hf ∈ Sdiag := h' ▸ (by simp [Sfull, T])
  exact hxy (by simpa [Sdiag] using hmem.2)

/-! ## The site -/

/-- The underlying category of the site: the skeleton of the category of finite sets, a small
category whose objects are the natural numbers. -/
abbrev Site : Type := FintypeCat.Skeleton.{0}

instance : HasTerminal Site :=
  Adjunction.hasLimitsOfShape_of_equivalence FintypeCat.Skeleton.equivalence.functor

instance : HasPullbacks Site :=
  Adjunction.hasLimitsOfShape_of_equivalence FintypeCat.Skeleton.equivalence.functor

/-- The forgetful functor of the site to sets, `n ↦ {0, …, n - 1}`. It commutes with finite
limits. -/
noncomputable abbrev forget : Site ⥤ Type :=
  FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.incl

/-- The functor `u` of the example: a finite set goes to the set of its nonempty subsets. -/
noncomputable abbrev u : Site ⥤ Type := forget ⋙ nonemptySubsets

lemma u_pullbackComparison {U V W : Site} (f : U ⟶ W) (g : V ⟶ W) :
    pullbackComparison u f g = nonemptySubsets.map (pullbackComparison forget f g) ≫
      pullbackComparison nonemptySubsets (forget.map f) (forget.map g) :=
  pullbackComparison_comp forget nonemptySubsets f g

lemma forget_pullbackComparison_bijective {U V W : Site} (f : U ⟶ W) (g : V ⟶ W) :
    Function.Bijective (nonemptySubsets.map (pullbackComparison forget f g)) :=
  (isIso_iff_bijective _).mp inferInstance

/-- Condition (2) for `u`. -/
theorem u_pullbackComparison_surjective {U V W : Site} (f : U ⟶ W) (g : V ⟶ W) :
    Function.Surjective (pullbackComparison u f g) := by
  rw [u_pullbackComparison]
  exact (nonemptySubsets_pullbackComparison_surjective _ _).comp
    (forget_pullbackComparison_bijective f g).2

/-- Condition (1) for `u`: `u` of the final object is a singleton. -/
@[instance_reducible]
noncomputable def uniqueUTerminal : Unique (u.obj (⊤_ Site)) := by
  have : Unique (forget.obj (⊤_ Site)) :=
    Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj forget)
  refine ⟨⟨⟨Set.univ, Set.univ_nonempty⟩⟩, fun A => Subtype.ext ?_⟩
  obtain ⟨a, ha⟩ := A.2
  exact Set.eq_univ_of_forall fun b => Subsingleton.elim a b ▸ ha

/-- The object `{0, 1}` of the site. -/
abbrev two : Site := FintypeCat.Skeleton.mk 2

/-- `u` does not commute with the product `{0, 1} × {0, 1}`. -/
theorem u_not_preservesLimit :
    ¬ PreservesLimit (cospan (terminal.from two) (terminal.from two)) u := by
  intro h
  have hinj : Function.Injective (pullbackComparison u (terminal.from two) (terminal.from two)) :=
    ((isIso_iff_bijective _).mp inferInstance).1
  rw [u_pullbackComparison] at hinj
  have : Unique (forget.obj (⊤_ Site)) :=
    Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj forget)
  refine nonemptySubsets_pullbackComparison_not_injective (forget.map (terminal.from two))
    (x := ULift.up (0 : Fin 2)) (y := ULift.up (1 : Fin 2))
    (fun e => absurd (congrArg ULift.down e) (by decide)) (Subsingleton.elim _ _)
    fun a b hab => ?_
  obtain ⟨a, rfl⟩ := (forget_pullbackComparison_bijective _ _).2 a
  obtain ⟨b, rfl⟩ := (forget_pullbackComparison_bijective _ _).2 b
  rw [hinj hab]

/-- No point of the site with the trivial topology has fiber functor `u`: the fiber functor of
a point commutes with finite limits. -/
theorem not_exists_point_fiber_iso_u :
    ¬ ∃ Φ : (⊥ : GrothendieckTopology Site).Point.{0}, Nonempty (Φ.fiber ≅ u) := by
  rintro ⟨Φ, ⟨e⟩⟩
  exact u_not_preservesLimit (preservesLimit_of_natIso _ e)

/-- By Stacks 00Y6, the composite of the Yoneda embedding with the stalk functor of `u` is `u`. -/
noncomputable def thetaIso : u ≅ yoneda ⋙ presheafStalk u :=
  NatIso.ofComponents (fun U => (Equiv.ofBijective _ (Phi_bijective u U)).toIso)
    (fun g => by ext x; exact Phi_naturality u g x)

/-- The stalk functor `Sh(C) ⥤ Set`, `F ↦ F_p`, of `u` on the site with the trivial topology is
not left exact. -/
theorem stalk_not_leftExact :
    ¬ PreservesFiniteLimits (sheafToPresheaf (⊥ : GrothendieckTopology Site) Type ⋙
      presheafStalk u) := by
  intro h
  -- every presheaf is a sheaf for `⊥`, so the Yoneda embedding lands in sheaves
  let Y : Site ⥤ Sheaf (⊥ : GrothendieckTopology Site) Type :=
    yoneda ⋙ (sheafBotEquivalence Type).inverse
  have : PreservesLimit (cospan (terminal.from two) (terminal.from two))
      (Y ⋙ sheafToPresheaf ⊥ Type ⋙ presheafStalk u) := inferInstance
  exact u_not_preservesLimit (@preservesLimit_of_natIso _ _ _ _ _ _ _
    (Y ⋙ sheafToPresheaf ⊥ Type ⋙ presheafStalk u) u
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft yoneda (sheafBotEquivalence Type).counitIso)
      (presheafStalk u) ≪≫ thetaIso.symm) this)

/-- **Stacks 00YD.** There is a site `C` with a final object and fibre products, and a functor
`u : C ⥤ Set` such that

1. `u(⊤) = {*}` is a singleton,
2. for every pair `U → W ← V` the map `u(U ×_W V) → u(U) ×_{u(W)} u(V)` is surjective,
3. for every covering `{U_i → U}` the map `∐ u(U_i) → u(U)` is surjective,

but `u` is not a point: no point of `C` (Stacks 00Y5) has fiber functor `u`, and the stalk
functor `Sh(C) ⥤ Set`, `F ↦ F_p` (Stacks 04EH), is not left exact.

The example is the skeleton of the category of finite sets with the trivial topology and `u` the
nonempty-subsets functor; the example given in the source fails (2). -/
@[stacks 00YD "the remark's assertion. The source's example (two objects `U → X`, `u(U)` with two
  elements) fails (2) at `U ×_X U = U`; corrected example: finite sets with the trivial topology and
  `u` the nonempty-subsets functor"]
theorem exists_site_weakly_left_exact_not_point :
    ∃ (C : Type) (_ : SmallCategory C) (J : GrothendieckTopology C) (_ : HasTerminal C)
      (_ : HasPullbacks C) (u : C ⥤ Type),
      Nonempty (Unique (u.obj (⊤_ C))) ∧
      (∀ {U V W : C} (f : U ⟶ W) (g : V ⟶ W), Function.Surjective (pullbackComparison u f g)) ∧
      (∀ {I : Type} {U : C} {Ui : I → C} (f : ∀ i, Ui i ⟶ U), Sieve.ofArrows Ui f ∈ J U →
        ∀ x : u.obj U, ∃ (i : I) (y : u.obj (Ui i)), u.map (f i) y = x) ∧
      (¬ ∃ Φ : J.Point.{0}, Nonempty (Φ.fiber ≅ u)) ∧
      ¬ PreservesFiniteLimits (sheafToPresheaf J Type ⋙ presheafStalk u) := by
  refine ⟨Site, inferInstance, ⊥, inferInstance, inferInstance, u, ⟨uniqueUTerminal⟩,
    u_pullbackComparison_surjective, fun f hf x => ?_, not_exists_point_fiber_iso_u,
    stalk_not_leftExact⟩
  refine Functor.CoveringJointlySurjective.ofArrows (J := ⊥) (fun U R hR x => ?_) f hf x
  rw [GrothendieckTopology.bot_covering] at hR
  exact ⟨U, 𝟙 U, hR ▸ trivial, x, Functor.map_id_apply u U x⟩

end CategoryTheory.WeakPullbacksNotPoint
