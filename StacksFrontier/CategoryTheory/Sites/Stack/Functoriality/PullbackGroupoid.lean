module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackFibred

/-! # The localization `u_p 𝒮` is fibred in groupoids when `𝒮` is

Notation and assumptions are those of Stacks 04WG, as set up in
`StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackFibred`: `u : 𝒞 ⥤ 𝒟` is a functor
commuting with nonempty finite limits, `𝒞` has nonempty finite limits, `p : 𝒮 ⥤ 𝒞` is a category
over `𝒞`, `u_pp 𝒮 = Comma (𝟭 𝒟) (p ⋙ u)`, `R = Comma.idBaseStronglyCartesian p u` is the set of
morphisms `(a, id_V, α)` of Stacks 04WF, `u_p 𝒮 = R⁻¹ u_pp 𝒮 = Comma.pullbackLocalization p u`, and
`p_p = Comma.pullbackProj p u : u_p 𝒮 ⥤ 𝒟` is the structure functor.

Stacks 04WH says that if `p` is fibred in *groupoids* then so is `p_p`. Following the source, the
proof combines Stacks 04WG (`Comma.isFibered_pullbackProj`: `p_p` is fibred) with Stacks 003V
(`CategoryTheory.Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid`), so all that has
to be added is that the fibres of `p_p` are groupoids.

## Main results

* `CategoryTheory.Comma.isFiberedInGroupoids_pullbackProj`: `p_p` is fibred in groupoids
  (Stacks 04WH).

## Implementation notes

The fibres are groupoids because *every* morphism of `u_p 𝒮` lying over an isomorphism of `𝒟` is an
isomorphism (`Comma.isIso_of_isIso_map_pullbackProj`), and a morphism of the fibre over `V` lies
over `𝟙 V`. That statement is where the hypothesis on `p` is used, and it comes out of two
observations.

*Every* morphism of `u_pp 𝒮` whose `𝒟`-component is an identity now lies in `R`: membership in `R`
asks in addition that the `𝒮`-component be strongly cartesian, and by Stacks 003V
(`CategoryTheory.Functor.IsFiberedInGroupoids.isStronglyCartesian`) every morphism of a category
fibred in groupoids is strongly cartesian over its own image. This is the sense in which, as the
source puts it, `R` becomes everything of the relevant shape.

Consequently a morphism `f : Z ⟶ X` of `u_pp 𝒮` whose `𝒟`-component is an *isomorphism* becomes
invertible in `u_p 𝒮`: it factors as
`Z --(id, f.left⁻¹-free part)--> (Z.left, x, f.left ∘ φ) --(id_U, f.left, id_x)--> X`, the first
factor having `𝒟`-component the identity, hence lying in `R`, and the second being the reindexing
morphism `Comma.baseChangeHom`, whose image in `u_p 𝒮` is strongly cartesian over `f.left` by
Stacks 04WG (`Comma.isStronglyCartesian_Q_baseChangeHom`) and therefore an isomorphism because
`f.left` is. A general morphism `χ` of `u_p 𝒮` is a right fraction `Q(s)⁻¹ ∘ Q(f)` by the calculus
of fractions of Stacks 04WF, and the `𝒟`-component of `f` is `s.left ∘ p_p(χ)`, an isomorphism as
soon as `p_p(χ)` is.

Faithfulness. The predicate proved is the project's canonical
`CategoryTheory.Functor.IsFiberedInGroupoids` (Stacks 003S), applied to the 04WG functor
`Comma.pullbackProj p u` itself; no local definition restates it and nothing is weakened to a
`Nonempty`. The hypothesis "`𝒮` is fibred in groupoids" is `p.IsFiberedInGroupoids`, which is a
`structure` and not a class, so it is an explicit hypothesis `hp`; the remaining hypotheses are
verbatim those of `Comma.isFibered_pullbackProj`, with `[p.IsFibered]` dropped because it follows
from `hp` (`CategoryTheory.Functor.IsFiberedInGroupoids.isFibered`).

Universes. `𝒞 : Type u₁` with `Category.{v₁}`, `𝒟 : Type u₂` with `Category.{v₂}` and
`𝒮 : Type u₃` with `Category.{v₃}` are three independent pairs, exactly as in `PullbackFibred`, and
none needs bounding: `Functor.IsFiberedInGroupoids` and `IsGroupoid` are `Prop`-valued and relate
the universes of a functor's source and target no more than `Functor.IsFibered` does, and
`Functor.Fiber p_p V` is a subtype of the objects of `u_p 𝒮`, so it introduces no new universe.

## References

* [StacksProject 04WH](https://stacks.math.columbia.edu/tag/04WH)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]

namespace Comma

variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)

/-- When `p` is fibred in groupoids, a morphism of `u_pp 𝒮` belongs to the set `R` of Stacks 04WF
as soon as its `𝒟`-component is an identity: the second requirement, that the `𝒮`-component be
strongly cartesian, is automatic by Stacks 003V. -/
lemma idBaseStronglyCartesian_of_left_eqToHom (hp : p.IsFiberedInGroupoids)
    {X Y : Comma (𝟭 𝒟) (p ⋙ u)} (f : X ⟶ Y) (h : X.left = Y.left) (hl : f.left = eqToHom h) :
    idBaseStronglyCartesian p u f :=
  ⟨⟨h, hl⟩, hp.isStronglyCartesian f.right⟩

section

variable [HasNonemptyFiniteLimits 𝒞]

/-- A morphism of `u_pp 𝒮` whose `𝒟`-component is an isomorphism becomes an isomorphism in
`u_p 𝒮`. It factors as a morphism with identity `𝒟`-component — which lies in `R`, by
`Comma.idBaseStronglyCartesian_of_left_eqToHom` — followed by the reindexing morphism
`Comma.baseChangeHom`, whose image is strongly cartesian over the `𝒟`-component by Stacks 04WG and
hence invertible. -/
lemma isIso_Q_map_of_isIso_left (hp : p.IsFiberedInGroupoids)
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    {Z X : Comma (𝟭 𝒟) (p ⋙ u)} (f : Z ⟶ X) [IsIso f.left] :
    IsIso ((idBaseStronglyCartesian p u).Q.map f) := by
  have := hp.isFibered
  obtain ⟨g, hgl, hgf⟩ :
      ∃ g : Z ⟶ Comma.mk Z.left X.right (f.left ≫ X.hom),
        g.left = 𝟙 Z.left ∧ g ≫ baseChangeHom p u X f.left = f := by
    refine ⟨⟨𝟙 Z.left, f.right, by simpa using f.w⟩, rfl, Comma.hom_ext _ _ ?_ ?_⟩
    · simp
    · simp
  have hgR : idBaseStronglyCartesian p u g :=
    idBaseStronglyCartesian_of_left_eqToHom p u hp g rfl (by rw [hgl]; simp)
  have h₁ : IsIso ((idBaseStronglyCartesian p u).Q.map g) :=
    Localization.inverts _ (idBaseStronglyCartesian p u) _ hgR
  have := isStronglyCartesian_Q_baseChangeHom p u hu X f.left
  have h₂ : IsIso ((idBaseStronglyCartesian p u).Q.map (baseChangeHom p u X f.left)) :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := pullbackProj p u) (f := f.left) _
  have hcomp : IsIso ((idBaseStronglyCartesian p u).Q.map (g ≫ baseChangeHom p u X f.left)) := by
    rw [Functor.map_comp]; infer_instance
  rwa [hgf] at hcomp

/-- **Every morphism of `u_p 𝒮` lying over an isomorphism of `𝒟` is an isomorphism**, when `p` is
fibred in groupoids. Writing the morphism as a right fraction `Q(s)⁻¹ ∘ Q(f)` (Stacks 04WF), the
`𝒟`-component of the numerator `f` is invertible, so `Q(f)` is invertible by
`Comma.isIso_Q_map_of_isIso_left`. -/
lemma isIso_of_isIso_map_pullbackProj (hp : p.IsFiberedInGroupoids)
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    {a b : pullbackLocalization p u} (χ : a ⟶ b) [IsIso ((pullbackProj p u).map χ)] :
    IsIso χ := by
  have := hp.isFibered
  have := hasRightCalculusOfFractions_idBaseStronglyCartesian p u hu
  have hQ : ∀ c, ∃ Z, (idBaseStronglyCartesian p u).Q.obj Z = c := fun c =>
    ⟨_, (Localization.Construction.objEquiv (idBaseStronglyCartesian p u)).apply_symm_apply c⟩
  obtain ⟨Z, rfl⟩ := hQ a
  obtain ⟨X, rfl⟩ := hQ b
  obtain ⟨ϕ, hϕ⟩ := Localization.exists_rightFraction
    (idBaseStronglyCartesian p u).Q (idBaseStronglyCartesian p u) χ
  have hϕs : (idBaseStronglyCartesian p u).Q.map ϕ.s ≫ χ =
      (idBaseStronglyCartesian p u).Q.map ϕ.f := by
    rw [hϕ]; exact MorphismProperty.RightFraction.map_s_comp_map ϕ _ _
  have hsiso : IsIso ((idBaseStronglyCartesian p u).Q.map ϕ.s) :=
    Localization.inverts _ (idBaseStronglyCartesian p u) _ ϕ.hs
  have hs' : (∃ h : ϕ.X'.left = Z.left, ϕ.s.left = eqToHom h) ∧
      stronglyCartesianOver p ϕ.s.right := ϕ.hs
  obtain ⟨⟨hsl, hsleft⟩, -⟩ := hs'
  have hleft : ϕ.s.left ≫ (pullbackProj p u).map χ = ϕ.f.left := by
    have d := congrArg (fun t => (pullbackProj p u).map t) hϕs
    simpa using d
  have hfleft : IsIso ϕ.f.left := by rw [← hleft, hsleft]; infer_instance
  have hfiso : IsIso ((idBaseStronglyCartesian p u).Q.map ϕ.f) :=
    isIso_Q_map_of_isIso_left p u hp hu ϕ.f
  have : IsIso ((idBaseStronglyCartesian p u).Q.map ϕ.s ≫ χ) := by rw [hϕs]; infer_instance
  exact IsIso.of_isIso_comp_left ((idBaseStronglyCartesian p u).Q.map ϕ.s) χ

/-- **The fibres of `p_p : u_p 𝒮 ⥤ 𝒟` are groupoids**, when `p` is fibred in groupoids: a morphism
of the fibre over `V` lies over `𝟙 V`, hence over an isomorphism, hence is an isomorphism of
`u_p 𝒮` by `Comma.isIso_of_isIso_map_pullbackProj`; its inverse again lies over `𝟙 V`, so it is a
morphism of the fibre. -/
lemma isGroupoid_fiber_pullbackProj (hp : p.IsFiberedInGroupoids)
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (V : 𝒟) : IsGroupoid ((pullbackProj p u).Fiber V) where
  all_isIso {x y} χ := by
    have hmap : IsIso ((pullbackProj p u).map (Functor.Fiber.fiberInclusion.map χ)) := by
      rw [IsHomLift.fac' (pullbackProj p u) (𝟙 V) (Functor.Fiber.fiberInclusion.map χ)]
      infer_instance
    have hiso : IsIso (Functor.Fiber.fiberInclusion.map χ) :=
      isIso_of_isIso_map_pullbackProj p u hp hu _
    refine ⟨⟨⟨inv (Functor.Fiber.fiberInclusion.map χ), inferInstance⟩, ?_, ?_⟩⟩
    all_goals
      apply Functor.Fiber.fiberInclusion.map_injective
      simp only [Functor.map_comp, Functor.map_id]
    · exact IsIso.hom_inv_id _
    · exact IsIso.inv_hom_id _

/-- **`u_p 𝒮` is fibred in groupoids over `𝒟`** (Stacks 04WH). With notation and assumptions as in
Stacks 04WG — `u : 𝒞 ⥤ 𝒟` a functor commuting with nonempty finite limits, `𝒞` with nonempty finite
limits, and `u_p 𝒮 = R⁻¹ u_pp 𝒮` the localization of `u_pp 𝒮 = Comma (𝟭 𝒟) (p ⋙ u)` at the set `R`
of Stacks 04WF, regarded as a category over `𝒟` through `p_p = Comma.pullbackProj p u` — if
`p : 𝒮 ⥤ 𝒞` is fibred in groupoids then so is `p_p`.

By Stacks 04WG the functor `p_p` is fibred, and its fibres are groupoids
(`Comma.isGroupoid_fiber_pullbackProj`), so this is Stacks 003V. -/
@[stacks 04WH]
theorem isFiberedInGroupoids_pullbackProj (hp : p.IsFiberedInGroupoids)
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u) :
    (pullbackProj p u).IsFiberedInGroupoids := by
  have := hp.isFibered
  have := isFibered_pullbackProj p u hu
  exact Functor.IsFiberedInGroupoids.mk' (isGroupoid_fiber_pullbackProj p u hp hu)

end

end Comma

end CategoryTheory
