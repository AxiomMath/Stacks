module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismCommute
public import StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology

/-!
# The transition of Stacks 07YA on infinitesimal automorphisms is bijective

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` satisfying
(RS*), let `y ⟶ x` be a morphism of charted objects lying over a ring map `A ⟶ C`, and let
`M ⟶ N` be a semilinear map of coefficients which is bijective. The transition of
Stacks 07YA on infinitesimal automorphisms carries an automorphism `θ` of the trivial lift of
`x` over `Spec A[M]` to the automorphism of the trivial lift of `y` over `Spec C[N]` obtained
by conjugating `θ` with a cartesian arrow over `Spec C[N] ⟶ Spec A[M]`; this is the relation
`Deformation.Artin.IsInfinitesimalAutomorphismBaseChange`. This file proves that any map
realizing that relation is bijective, which is the Rim–Schlessinger step of Stacks 07YT on
infinitesimal automorphisms.

There are two halves. The relation does not visibly determine the transition: a cartesian
arrow realizing it is unique only up to an automorphism of the trivial lift of `y`, so two
maps realizing it differ by a conjugation. Since the automorphisms of a trivial lift commute
(`Deformation.Artin.comp_comm_infinitesimalAutomorphism`, the Eckmann–Hilton half of
Stacks 06I6) that conjugation is trivial, and the relation *is* single-valued:
`Deformation.Artin.eq_of_isInfinitesimalAutomorphismBaseChange`. The other half produces one
bijection realizing the relation, out of the (RS*) equivalence of the categories of lifts
across the square `A[M] = A ×_C C[N]`: the equivalence is fully faithful, hence bijective on
the automorphisms of a lift, and the comparison it carries is conjugation by the chosen
cartesian arrow.

## Main results

* `Deformation.Artin.exists_bijective_underEndBaseChange` — across a square of the base whose
  comparison functor is an equivalence, conjugation by a cartesian arrow is a bijection from
  the automorphisms of a lift of `x` over the fourth corner to the automorphisms of a lift of
  `y` over the third.
* `Deformation.Artin.eq_of_isInfinitesimalAutomorphismBaseChange` — the transition of
  Stacks 07YA on infinitesimal automorphisms is single-valued.
* `Deformation.Artin.bijective_of_isInfinitesimalAutomorphismBaseChange` — **every map
  realizing the transition of Stacks 07YA on infinitesimal automorphisms at a bijective
  semilinear map of coefficients is bijective.**

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07YT](https://stacks.math.columbia.edu/tag/07YT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Under.post

universe u v w

namespace Deformation.Artin

/-! ### Automorphisms of a lift across an (RS*) square -/

section SquareEnd

open CategoryTheory.Functor

variable {C : Type*} [Category C] {D : Type*} [Category D] (p : D ⥤ C)
  (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
  {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (hsq : f ≫ i = g ≫ j)

/-- A fully faithful functor is bijective on the endomorphisms of an object. -/
public theorem bijective_map_end {E₁ E₂ : Type*} [Category E₁] [Category E₂] (G : E₁ ⥤ E₂)
    [G.Full] [G.Faithful] (t : E₁) : Function.Bijective (fun u : t ⟶ t => G.map u) :=
  ⟨fun _ _ huv => G.map_injective huv, fun v => ⟨G.preimage v, G.map_preimage v⟩⟩

/-- The underlying arrow of a composite of morphisms of lifts. -/
public theorem underFiber_comp_right {z : D} {T : Under (p.obj z)}
    {s t r : (Under.post p).Fiber T} (α : s ⟶ t) (β : t ⟶ r) :
    (α ≫ β).1.right = α.1.right ≫ β.1.right := rfl

/-- A morphism of lifts out of an arrow of the ambient category which lies over the identity
and is compatible with the two structure arrows. -/
public def underFiberHomOfRight {z : D} {T : Under (p.obj z)} {s t : (Under.post p).Fiber T}
    (m : s.1.right ⟶ t.1.right) (hm : p.IsHomLift (𝟙 T.right) m)
    (hcompat : s.1.hom ≫ m = t.1.hom) : s ⟶ t := by
  refine ⟨Under.homMk m hcompat, IsHomLift.of_fac' _ _ _ s.2 t.2 ?_⟩
  apply Under.UnderMorphism.ext
  change p.map m = _
  have := hm
  simp only [Under.comp_right, Under.eqToHom_right, Under.id_right]
  exact IsHomLift.fac' p (𝟙 T.right) m

/-- The underlying arrow of `Deformation.Artin.underFiberHomOfRight`. -/
public theorem underFiberHomOfRight_right {z : D} {T : Under (p.obj z)}
    {s t : (Under.post p).Fiber T} (m : s.1.right ⟶ t.1.right)
    (hm : p.IsHomLift (𝟙 T.right) m) (hcompat : s.1.hom ≫ m = t.1.hom) :
    (underFiberHomOfRight p m hm hcompat).1.right = m := rfl

include hsq in
/-- **The (RS*) equivalence on the automorphisms of a lift.** The chosen pullback along the
remaining leg of the square carries the automorphisms of a lift of `x` over the fourth corner
bijectively to the automorphisms of a lift of `y` over the third, by conjugation with the
chosen cartesian arrow. -/
public theorem exists_chosenPullback_underEndBaseChange
    (hE : (fiberSquareComparison p c f g i j hsq).IsEquivalence)
    (x : p.Fiber V) (y : p.Fiber U) (η : y.1 ⟶ x.1) (hη : p.IsCartesian f η)
    (t : (c.pullbackFunctor i).IsoFiber x) :
    ∃ (b : (Under.post p).Fiber (Under.mk (eqToHom y.2 ≫ g)))
      (ρ : b.1.right ⟶ ((isoFiberToUnder p c i x).obj t).1.right),
      p.IsStronglyCartesian j ρ ∧
      b.1.hom ≫ ρ = η ≫ ((isoFiberToUnder p c i x).obj t).1.hom ∧
      ∃ Λ : (t ⟶ t) → (b ⟶ b), Function.Bijective Λ ∧
        ∀ u : t ⟶ t,
          (Λ u).1.right ≫ ρ = ρ ≫ ((isoFiberToUnder p c i x).map u).1.right := by
  have := isoFiberCongrBase_full (c.pullbackFunctor g)
    (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)
  have := isoFiberCongrBase_faithful (c.pullbackFunctor g)
    (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)
  refine ⟨isoFiberToUnderObj p c g y ((isoFiberCongrBase (c.pullbackFunctor g)
      (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)).obj
      ((squareLiftEquivalence p c f g i j hsq hE x).functor.obj t)),
    c.map j t.obj.left, c.isStronglyCartesian j t.obj.left,
    isoFiberArrow_isoFiberCongrBase_squareLiftEquivalence_fac p c f g i j hsq hE x y η hη t,
    fun u => (isoFiberToUnder p c g y).map
      ((isoFiberCongrBase (c.pullbackFunctor g)
          (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)).map
        ((squareLiftEquivalence p c f g i j hsq hE x).functor.map u)), ?_,
    fun u => c.homMap_fac j u.hom.left⟩
  · exact (isoFiberToUnder_map_bijective p c g y _).comp
      ((bijective_map_end (isoFiberCongrBase (c.pullbackFunctor g)
          (fiberIsoOfCartesian f (c.map f x) η inferInstance hη)) _).comp
        (bijective_map_end (squareLiftEquivalence p c f g i j hsq hE x).functor t))

include hp hsq in
/-- **The (RS*) comparison on automorphisms of a lift.** Let the comparison functor of a
square of the base be an equivalence, let `η : y ⟶ x` be cartesian over the first leg, let `a`
be a lift of `x` along the arrow into the fourth corner, let `b` be a lift of `y` along the
other branch, and let `ρ : b ⟶ a` be a cartesian arrow over the remaining leg compatible with
`η`. Then conjugation by `ρ` is a bijection from the automorphisms of `a` to those of `b`. -/
public theorem exists_bijective_underEndBaseChange
    (hE : (fiberSquareComparison p c f g i j hsq).IsEquivalence)
    (x : p.Fiber V) (y : p.Fiber U) (η : y.1 ⟶ x.1) (hη : p.IsCartesian f η)
    (a : (Under.post p).Fiber (Under.mk (eqToHom x.2 ≫ i)))
    (b : (Under.post p).Fiber (Under.mk (eqToHom y.2 ≫ g)))
    (ρ : b.1.right ⟶ a.1.right) (hρ : p.IsStronglyCartesian j ρ)
    (hfac : b.1.hom ≫ ρ = η ≫ a.1.hom) :
    ∃ τ : (a ⟶ a) → (b ⟶ b), Function.Bijective τ ∧
      ∀ θ : a ⟶ a, (τ θ).1.right ≫ ρ = ρ ≫ θ.1.right := by
  obtain ⟨t, rfl⟩ := isoFiberToUnder_surjective p hp c i x a
  obtain ⟨b₁, ρ₁, hρ₁, hfac₁, Λ, hΛbij, hΛ⟩ :=
    exists_chosenPullback_underEndBaseChange p c f g i j hsq hE x y η hη t
  -- The two cartesian arrows differ by an isomorphism of the fibre over the third corner.
  let bf : p.Fiber W := ⟨b.1.right, congrArg Under.right b.2⟩
  let b₁f : p.Fiber W := ⟨b₁.1.right, congrArg Under.right b₁.2⟩
  have hρc : p.IsCartesian j ρ := hρ.isCartesian_of_isStronglyCartesian
  have hρ₁c : p.IsCartesian j ρ₁ := hρ₁.isCartesian_of_isStronglyCartesian
  obtain ⟨e, he⟩ : ∃ e : bf ≅ b₁f, Fiber.fiberInclusion.map e.hom ≫ ρ₁ = ρ :=
    ⟨fiberIsoOfCartesian j ρ ρ₁ hρc hρ₁c,
      fiberIsoOfCartesian_hom_fac (z := bf) (z' := b₁f) j ρ ρ₁ hρc hρ₁c⟩
  -- That isomorphism is an isomorphism of lifts of `y`.
  have hehom : p.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map e.hom) := e.hom.2
  have hcomp : p.IsHomLift g (b.1.hom ≫ Fiber.fiberInclusion.map e.hom) := by
    have := underFiber_isHomLift p y.2 g b
    exact IsHomLift.comp_lift_id_right p g b.1.hom (Fiber.fiberInclusion.map e.hom)
  have hcompat : b.1.hom ≫ Fiber.fiberInclusion.map e.hom = b₁.1.hom := by
    have := underFiber_isHomLift p y.2 g b₁
    refine IsStronglyCartesian.ext p j ρ₁ g ?_
    rw [Category.assoc, he, hfac, hfac₁]
  let em : b ⟶ b₁ := underFiberHomOfRight p (Fiber.fiberInclusion.map e.hom) hehom hcompat
  have : CategoryTheory.IsGroupoid ((Under.post p).Fiber
      (Under.mk (eqToHom y.2 ≫ g) : Under (p.obj y.1))) :=
    (underPost_isFiberedInGroupoids p hp y.1).fiber_isGroupoid _
  have : IsIso em := CategoryTheory.IsGroupoid.all_isIso em
  -- Conjugating the (RS*) bijection by it.
  let φ₀ : (t ⟶ t) ≃ ((isoFiberToUnder p c i x).obj t ⟶ (isoFiberToUnder p c i x).obj t) :=
    Equiv.ofBijective _ (isoFiberToUnder_map_bijective p c i x t)
  refine ⟨fun θ => (conjEndEquiv (asIso em)).symm (Λ (φ₀.symm θ)), ?_, ?_⟩
  · exact (conjEndEquiv (asIso em)).symm.bijective.comp (hΛbij.comp φ₀.symm.bijective)
  · intro θ
    obtain ⟨u, rfl⟩ := φ₀.surjective θ
    have hW : (Λ u).1.right ≫ ρ₁ = ρ₁ ≫ (φ₀ u).1.right := hΛ u
    have hhe : (asIso em).hom.1.right ≫ ρ₁ = ρ := he
    have hinvhom : (asIso em).inv.1.right ≫ (asIso em).hom.1.right = 𝟙 b₁.1.right :=
      congrArg (fun z : b₁ ⟶ b₁ => z.1.right) (asIso em).inv_hom_id
    have hinvρ : (asIso em).inv.1.right ≫ ρ = ρ₁ := by
      rw [← hhe, ← Category.assoc, hinvhom, Category.id_comp]
    change ((asIso em).hom ≫ Λ (φ₀.symm (φ₀ u)) ≫ (asIso em).inv).1.right ≫ ρ =
      ρ ≫ (φ₀ u).1.right
    rw [Equiv.symm_apply_apply, underFiber_comp_right, underFiber_comp_right, Category.assoc,
      Category.assoc, hinvρ, hW, ← Category.assoc, hhe]

end SquareEnd

/-! ### The transition of Stacks 07YA on infinitesimal automorphisms -/

section ChartedInf

open CategoryTheory.Functor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}

/-- **The transition of Stacks 07YA on infinitesimal automorphisms is single-valued.** A
cartesian arrow realizing the transition is unique only up to an automorphism of the trivial
lift of `y`, so two automorphisms realizing the transition at one and the same `θ` are
conjugate; since the infinitesimal automorphisms commute they are equal. -/
public theorem eq_of_isInfinitesimalAutomorphismBaseChange (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {P Q : ChartedObject B S hS p c} (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    {θ : P.trivialLift hp M ⟶ P.trivialLift hp M}
    {χ χ' : Q.trivialLift hp N ⟶ Q.trivialLift hp N}
    (hχ : IsInfinitesimalAutomorphismBaseChange hp h f ψ θ χ)
    (hχ' : IsInfinitesimalAutomorphismBaseChange hp h f ψ θ χ') :
    χ = χ' := by
  obtain ⟨g, hg, ρ, hρ, hfac, hcj⟩ := hχ
  obtain ⟨g', hg', ρ', hρ', hfac', hcj'⟩ := hχ'
  have : p.IsStronglyCartesian g ρ' := by
    rw [← eq_of_isSquareZeroBaseMap hg' hg]
    exact hρ'
  have hid : g = 𝟙 (Q.squareZeroBase N) ≫ g := (Category.id_comp g).symm
  have hεfac : IsStronglyCartesian.map p g ρ hid ρ' ≫ ρ = ρ' :=
    IsStronglyCartesian.fac p g ρ hid ρ'
  have hεhom : p.IsHomLift (𝟙 (Q.squareZeroBase N)) (IsStronglyCartesian.map p g ρ hid ρ') :=
    IsStronglyCartesian.map_isHomLift p g ρ hid ρ'
  have := isHomLift_fiberUnder_hom p
    (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N) Q.obj.obj
    (Q.trivialLift hp N)
  have hcompat : (Q.trivialLift hp N).1.hom ≫ IsStronglyCartesian.map p g ρ hid ρ' =
      (Q.trivialLift hp N).1.hom := by
    have : p.IsHomLift (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N)
        ((Q.trivialLift hp N).1.hom ≫ IsStronglyCartesian.map p g ρ hid ρ') :=
      IsHomLift.comp_lift_id_right p _ (Q.trivialLift hp N).1.hom
        (IsStronglyCartesian.map p g ρ hid ρ')
    refine IsStronglyCartesian.ext p g ρ
      (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N) ?_
    rw [Category.assoc, hεfac, hfac', hfac]
  have hχr : p.IsHomLift (𝟙 (Q.squareZeroBase N)) χ.1.right :=
    underPost_isHomLift_right p _ _ χ.2
  have hχ'r : p.IsHomLift (𝟙 (Q.squareZeroBase N)) χ'.1.right :=
    underPost_isHomLift_right p _ _ χ'.2
  have hconj : χ'.1.right ≫ IsStronglyCartesian.map p g ρ hid ρ' =
      IsStronglyCartesian.map p g ρ hid ρ' ≫ χ.1.right := by
    have : p.IsHomLift (𝟙 (Q.squareZeroBase N))
        (χ'.1.right ≫ IsStronglyCartesian.map p g ρ hid ρ') :=
      IsHomLift.comp_lift_id_right p _ χ'.1.right (IsStronglyCartesian.map p g ρ hid ρ')
    have : p.IsHomLift (𝟙 (Q.squareZeroBase N))
        (IsStronglyCartesian.map p g ρ hid ρ' ≫ χ.1.right) :=
      IsHomLift.comp_lift_id_right p _ (IsStronglyCartesian.map p g ρ hid ρ') χ.1.right
    refine IsStronglyCartesian.ext p g ρ (𝟙 (Q.squareZeroBase N)) ?_
    rw [Category.assoc, Category.assoc, hεfac, hcj', hcj, ← Category.assoc, hεfac]
  let εl : Q.trivialLift hp N ⟶ Q.trivialLift hp N :=
    underFiberHomOfRight p (IsStronglyCartesian.map p g ρ hid ρ') hεhom hcompat
  have hlift : χ' ≫ εl = εl ≫ χ := Fiber.hom_ext (Under.UnderMorphism.ext hconj)
  have hcomm := comp_comm_infinitesimalAutomorphism Q.ring B S hS Q.obj.alg.toScheme
    Q.obj.alg.mem p Q.point Q.obj.obj.2 hp hRS N χ' εl
  have : IsIso εl := isIso_infinitesimalAutomorphism Q.ring B S hS Q.obj.alg.toScheme
    Q.obj.alg.mem p Q.point Q.obj.obj.2 hp N εl
  exact ((cancel_epi εl).mp (hcomm.symm.trans hlift)).symm

/-- **The Rim–Schlessinger step of Stacks 07YT on infinitesimal automorphisms.** Let `y ⟶ x`
be a morphism of charted objects over a ring map `A ⟶ C` and let `M ⟶ N` be a bijective
semilinear map of coefficients. Then every map realizing the transition of Stacks 07YA on
infinitesimal automorphisms is bijective: the trivial square-zero extension `A[M]` is the
fibre product `A ×_C C[N]`, with the square-zero surjection `C[N] ⟶ C` on one side, so (RS*)
identifies the lifts of `x` over `Spec A[M]` with the lifts of `y` over `Spec C[N]`, hence
also their automorphisms. -/
public theorem bijective_of_isInfinitesimalAutomorphismBaseChange (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {P Q : ChartedObject B S hS p c} (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring)
    (halg : f = h.alg.ringMap)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (hψ : Function.Bijective (restrictScalarsAddHom f ψ))
    (σ : (P.trivialLift hp M ⟶ P.trivialLift hp M) →
      (Q.trivialLift hp N ⟶ Q.trivialLift hp N))
    (hσ : ∀ θ, IsInfinitesimalAutomorphismBaseChange hp h f ψ θ (σ θ)) :
    Function.Bijective σ := by
  have : p.IsFibered := hp.isFibered
  obtain ⟨g, hg, ρ, hρ, hfacρ, -⟩ := hσ (𝟙 (P.trivialLift hp M))
  obtain rfl : g = squareZeroOverBaseMap f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
      (specMap_toScheme_comp h f halg) M N (restrictScalarsAddHom f ψ)
      (restrictScalarsAddHom_smul f ψ) :=
    eq_of_isSquareZeroBaseMap hg (isSquareZeroBaseMap_squareZeroOverBaseMap h f halg ψ)
  have : p.IsHomLift (algebraOverMapOfRingHom f B S hS P.obj.alg.toScheme
      Q.obj.alg.toScheme P.obj.alg.mem Q.obj.alg.mem (specMap_toScheme_comp h f halg))
      h.objMap := specMap_eq_algebraOverMap h f halg ▸ h.objMap_isHomLift
  obtain ⟨τ, hτbij, hτ⟩ := exists_bijective_underEndBaseChange p hp (Functor.chosenPullbacks p)
    (algebraOverMapOfRingHom f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme P.obj.alg.mem
      Q.obj.alg.mem (specMap_toScheme_comp h f halg))
    (squareZeroArrow Q.ring B S hS Q.obj.alg.toScheme Q.obj.alg.mem N)
    (squareZeroArrow P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem M)
    (squareZeroOverBaseMap f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
      (specMap_toScheme_comp h f halg) M N (restrictScalarsAddHom f ψ)
      (restrictScalarsAddHom_smul f ψ))
    (algebraOverMap_comp_squareZeroArrow f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
      P.obj.alg.mem Q.obj.alg.mem (specMap_toScheme_comp h f halg) M N
      (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ))
    (baseChangeSquare_isEquivalence f B S hS P.obj.alg.toScheme Q.obj.alg.toScheme
      P.obj.alg.mem Q.obj.alg.mem (specMap_toScheme_comp h f halg) M N
      (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ) p hp hRS hψ)
    P.obj.obj Q.obj.obj h.objMap
    (hp.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian
    (P.trivialLift hp M) (Q.trivialLift hp N) ρ hρ hfacρ
  obtain rfl : σ = τ := funext fun θ =>
    eq_of_isInfinitesimalAutomorphismBaseChange hp hRS h f ψ (hσ θ)
      ⟨_, hg, ρ, hρ, hfacρ, hτ θ⟩
  exact hτbij

/-- **The Rim–Schlessinger step of Stacks 07YT on infinitesimal automorphisms, read through
chosen parametrisations.** The functor `Inf_x` of Stacks 07Y9 presents the automorphisms of
the trivial lift as the underlying set of a module through a bijection, and a map of those
modules realizes the transition of Stacks 07YA when it does so after both bijections; such a
map is bijective. -/
public theorem bijective_of_isInfinitesimalAutomorphismBaseChange_equiv
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    {P Q : ChartedObject B S hS p c} (h : AffineObject.Hom P.obj Q.obj) (f : P.ring →+* Q.ring)
    (halg : f = h.alg.ringMap)
    {M : SiteModule P.ring B} {N : SiteModule Q.ring B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (hψ : Function.Bijective (restrictScalarsAddHom f ψ))
    {TM TN : Type*} (eM : TM ≃ (P.trivialLift hp M ⟶ P.trivialLift hp M))
    (eN : TN ≃ (Q.trivialLift hp N ⟶ Q.trivialLift hp N)) (σ : TM → TN)
    (hσ : ∀ θ, IsInfinitesimalAutomorphismBaseChange hp h f ψ (eM θ) (eN (σ θ))) :
    Function.Bijective σ := by
  have key : Function.Bijective (fun θ' => eN (σ (eM.symm θ'))) :=
    bijective_of_isInfinitesimalAutomorphismBaseChange hp hRS h f halg ψ hψ _ fun θ' => by
      simpa only [Equiv.apply_symm_apply] using hσ (eM.symm θ')
  have hfac : σ = fun θ => eN.symm ((fun θ' => eN (σ (eM.symm θ'))) (eM θ)) := by
    funext θ
    simp
  rw [hfac]
  exact eN.symm.bijective.comp (key.comp eM.bijective)

end ChartedInf

end Deformation.Artin
