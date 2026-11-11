module

public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful

/-!
# The stackification of a fully faithful projection

Let `(𝒞, J)` be a site and let `p : 𝒜 ⥤ 𝒞` be a fibred category whose projection is full and
faithful, so that, up to equivalence, `𝒜` is `𝒞` fibred over itself by the identity. A
stackification `p' : ℬ ⥤ 𝒞` of `p` — a 1-morphism `G : 𝒜 ⥤ ℬ` satisfying the two clauses of
**Stacks 02ZN** into a stack — then has full and faithful projection too: the base, fibred over
itself, is already a stack, and the extension of the 1-morphism `p` along `G` is fully faithful by
**Stacks 04WQ** in the form `CategoryTheory.Functor.Stackification.full_of_extension`.

## Main results

* `CategoryTheory.Functor.Fiber.subsingleton_hom_of_faithful` and
  `CategoryTheory.Functor.Fiber.nonempty_hom_of_full`: the fibres of a full and faithful
  projection are indiscrete.
* `CategoryTheory.Functor.isMorSheaf_of_full_of_faithful` and
  `CategoryTheory.Functor.isFiberedInGroupoids_of_full_of_faithful`: a full and faithful functor
  with a section, such as the base fibred over itself, is a stack in groupoids for every topology.
* `CategoryTheory.Functor.Stackification.full_of_full_of_faithful` and
  `CategoryTheory.Functor.Stackification.faithful_of_full_of_faithful`: the projection of a
  stackification of a full and faithful projection is full and faithful.

## Implementation notes

`CategoryTheory.Functor.Stackification.full_of_extension` asks for its three fibred categories to
share one morphism universe, while the morphisms of the base may live in a smaller one. So the base
enters as any full and faithful `q : 𝒳 ⥤ 𝒞` with a section `s`, in the morphism universe of `p`;
for the quotient stacks of the library this is `CategoryTheory.ULiftHom 𝒞`, fibred over `𝒞` by
`CategoryTheory.ULiftHom.down`, with section `CategoryTheory.ULiftHom.up`. The extension is
`p' ⋙ s`.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
-/

@[expose] public section

namespace CategoryTheory

open Opposite

namespace Functor

universe vb v u₁ u₂ u₃ u₄

section Fiber

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] (r : 𝒮 ⥤ 𝒞)

/-- In a fibre of a faithful functor two morphisms with the same endpoints are equal: both lie
over the identity. -/
theorem Fiber.subsingleton_hom_of_faithful [r.Faithful] {U : 𝒞} (a b : r.Fiber U) :
    Subsingleton (a ⟶ b) := by
  constructor
  intro φ ψ
  have h₁ := IsHomLift.fac' r (𝟙 U) (Fiber.fiberInclusion.map φ)
  have h₂ := IsHomLift.fac' r (𝟙 U) (Fiber.fiberInclusion.map ψ)
  exact Fiber.hom_ext (r.map_injective (h₁.trans h₂.symm))

/-- In a fibre of a full functor any two objects are joined by a morphism: the preimage of the
identity of the base. -/
theorem Fiber.nonempty_hom_of_full [r.Full] {U : 𝒞} (a b : r.Fiber U) : Nonempty (a ⟶ b) := by
  let φ : a.1 ⟶ b.1 := r.preimage (eqToHom (a.2.trans b.2.symm))
  have : r.IsHomLift (𝟙 U) φ := IsHomLift.of_fac' r (𝟙 U) φ a.2 b.2 (by simp [φ])
  exact ⟨Fiber.homMk r U φ⟩

/-- Every presheaf of morphisms of a full and faithful functor is a sheaf: its sections are
morphisms of a fibre, of which there is exactly one between any two objects. -/
theorem isMorSheaf_of_full_of_faithful [r.Full] [r.Faithful] [r.IsFibered]
    (J : GrothendieckTopology 𝒞) (U : 𝒞) (x y : r.Fiber U) : IsMorSheaf r J U x y := by
  refine (isSheaf_iff_isSheaf_of_type _ _).2 fun {X} S _ _ _ => ?_
  obtain ⟨t⟩ := Fiber.nonempty_hom_of_full r (pullbackFiber r x X.hom) (pullbackFiber r y X.hom)
  exact ⟨t, fun _ _ _ => (Fiber.subsingleton_hom_of_faithful r _ _).elim _ _,
    fun _ _ => (Fiber.subsingleton_hom_of_faithful r _ _).elim _ _⟩

end Fiber

section Section

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₄} [Category.{v} 𝒳] (q : 𝒳 ⥤ 𝒞)
  [q.Full] [q.Faithful] (s : 𝒞 ⥤ 𝒳) (hs : s ⋙ q = 𝟭 𝒞)

include hs in
/-- A full and faithful functor with a section is fibred in groupoids. -/
theorem isFiberedInGroupoids_of_full_of_faithful : q.IsFiberedInGroupoids where
  exists_lift {V U} f x hx := by
    have e : q.obj (s.obj V) = V := Functor.congr_obj hs V
    let φ : s.obj V ⟶ x := q.preimage (eqToHom e ≫ f ≫ eqToHom hx.symm)
    exact ⟨s.obj V, φ, IsHomLift.of_fac' q f φ e hx (by simp [φ])⟩
  unique_lift {x y z} φ ψ f hf :=
    ⟨q.preimage f, ⟨q.map_preimage f, q.map_injective (by simpa using hf)⟩,
      fun χ hχ => q.map_injective (by simpa using hχ.1)⟩

end Section

namespace Stackification

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜]
  {ℬ : Type u₃} [Category.{v} ℬ] {𝒳 : Type u₄} [Category.{v} 𝒳]
  {p : 𝒜 ⥤ 𝒞} {p' : ℬ ⥤ 𝒞} [p.IsFibered] [p'.IsFibered] {G : 𝒜 ⥤ ℬ}
  (hG : p.IsFibredOneMorphism p' G) (J : GrothendieckTopology 𝒞)
  (hGmor : ∀ (U : 𝒞) (a b : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap a b) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap a b))
  (hGobj : ∀ (U : 𝒞) (x : p'.Fiber U), ∃ R ∈ J U,
    ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x f))
  (hp' : ∀ (U : 𝒞) (x y : p'.Fiber U), IsMorSheaf p' J U x y)
  (q : 𝒳 ⥤ 𝒞) [q.Full] [q.Faithful] (s : 𝒞 ⥤ 𝒳) (hs : s ⋙ q = 𝟭 𝒞)

include hGmor hGobj hp' hs

/-- The extension `p' ⋙ s` of `p` along `G`, a 1-morphism into the base fibred over itself by
`q`, is full and faithful, and it lies over the base. -/
private theorem full_faithful_comp_section [p.Full] [p.Faithful] :
    (p' ⋙ s).Full ∧ (p' ⋙ s).Faithful ∧ (p' ⋙ s) ⋙ q = p' := by
  have hq : q.IsFiberedInGroupoids := isFiberedInGroupoids_of_full_of_faithful q s hs
  have := hq.isFibered
  have hcomp : (p' ⋙ s) ⋙ q = p' := by rw [Functor.assoc, hs, Functor.comp_id]
  have hH : p'.IsFibredOneMorphism q (p' ⋙ s) :=
    { comp_eq := hcomp
      map_isStronglyCartesian := by
        intro R T f a b φ _
        have := isHomLift_map_of_comp_eq hcomp f φ
        exact hq.isStronglyCartesian_homLift f _ }
  have hFmor : ∀ (U : 𝒞) (a b : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) ((hG.comp hH).morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) ((hG.comp hH).morPresheafMap a b) := by
    intro U a b
    have happ : ∀ g, IsIso (((hG.comp hH).morPresheafMap a b).app g) := by
      intro g
      rw [isIso_iff_bijective]
      obtain ⟨m⟩ := Fiber.nonempty_hom_of_full p (pullbackFiber p a g.unop.hom)
        (pullbackFiber p b g.unop.hom)
      exact ⟨fun m₁ m₂ _ => (Fiber.subsingleton_hom_of_faithful p _ _).elim m₁ m₂,
        fun n => ⟨m, (Fiber.subsingleton_hom_of_faithful q _ _).elim _ n⟩⟩
    have : IsIso ((hG.comp hH).morPresheafMap a b) := NatIso.isIso_of_isIso_app _
    exact ⟨inferInstance, inferInstance⟩
  exact ⟨full_of_extension hG hH J hGmor hGobj hFmor hp' (isMorSheaf_of_full_of_faithful q J),
    faithful_of_extension hG hH J hGmor hGobj hFmor hp' (isMorSheaf_of_full_of_faithful q J),
    hcomp⟩

/-- **The projection of a stackification of a full and faithful projection is full.** -/
theorem full_of_full_of_faithful [p.Full] [p.Faithful] : p'.Full := by
  obtain ⟨_, _, hcomp⟩ := full_faithful_comp_section hG J hGmor hGobj hp' q s hs
  rw [← hcomp]
  infer_instance

/-- **The projection of a stackification of a full and faithful projection is faithful.** -/
theorem faithful_of_full_of_faithful [p.Full] [p.Faithful] : p'.Faithful := by
  obtain ⟨_, _, hcomp⟩ := full_faithful_comp_section hG J hGmor hGobj hp' q s hs
  rw [← hcomp]
  infer_instance

end Stackification

end Functor

end CategoryTheory
