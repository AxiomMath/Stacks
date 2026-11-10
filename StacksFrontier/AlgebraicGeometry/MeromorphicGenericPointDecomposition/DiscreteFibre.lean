module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicPullback
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Local
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

/-!
# Schemes flat over the codimension-zero points of an affine scheme

Let `X` be an affine scheme whose weakly associated points are generic points of irreducible
components and whose quasi-compact opens have finitely many irreducible components, and let
`T i ⟶ X` be a family of morphisms which are flat preimmersions — the shape of a base change of
`X` along the canonical morphism `Spec 𝒪_{X, η} ⟶ X` at a point `η` of codimension `0`.  Each
`T i` is then a *discrete* scheme whose points are codimension-zero points of `X`, and if the
resulting map `Σ i, T i ⟶ X⁰` is a bijection then

`∏ i, Γ(T i, 𝒪) = Q(Γ(X, 𝒪))`,

the total ring of fractions.  This is the affine-chart computation behind the description of the
sheaf of meromorphic functions as a product of direct images at the codimension-zero points.

## Main results

* `AlgebraicGeometry.isUnit_of_isRegularSectionOn_top_of_ringKrullDim_stalk_eq_zero`: on a scheme
  all of whose local rings have Krull dimension zero a regular global section is a unit.
* `AlgebraicGeometry.finite_and_discreteTopology_of_flat_isPreimmersion`: a scheme with
  zero-dimensional local rings which is a flat preimmersion over a scheme with finitely many
  generic points is finite and discrete.
* `AlgebraicGeometry.bijective_pi_germ_of_discreteTopology`: the global sections of a discrete
  scheme are the product of its local rings.
* `AlgebraicGeometry.isLocalization_pi_sections_of_genericPoints`: the product of the rings of
  global sections of such a family is the total ring of fractions of `Γ(X, 𝒪)`.

## Implementation notes

Flatness and the preimmersion property are the two properties of `Spec 𝒪_{X, η} ⟶ X` which pass
to a base change, and together they already force the morphism to induce isomorphisms on local
rings (`AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion`); so the hypotheses here are
stated for an arbitrary flat preimmersion rather than for a base change.  The discreteness of
`T i` comes from the local rings: a point with a zero-dimensional local ring is a maximal point
of the specialization order, so no two points of `T i` specialize to one another, and the space
is `T1`; finiteness comes from the injection into the generic points of `X`.

The identification of the total ring of fractions is reduced to the affine statement
`AlgebraicGeometry.isLocalization_pi_stalk_genericPoints` for `X` itself, taken on the open
`⊤`, by transporting along the bijection of the hypothesis.

## References

* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 02LX](https://stacks.math.columbia.edu/tag/02LX)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u v

namespace AlgebraicGeometry

/-- **On a scheme all of whose local rings have Krull dimension zero a regular global section is
a unit.** A regular section has nonzerodivisor germs, and in a zero-dimensional local ring every
nonzerodivisor is a unit; a section which is a unit in every local ring is a unit. -/
theorem isUnit_of_isRegularSectionOn_top_of_ringKrullDim_stalk_eq_zero (X : Scheme.{u})
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 0) (s : Γ(X, ⊤))
    (hs : IsRegularSectionOn X.toLocallyRingedSpace ⊤ s) : IsUnit s := by
  refine X.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ ⊤ s fun x hx => ?_
  have hreg := (Stacks.Meromorphic.isRegularSectionOn_iff_germ
    X.toLocallyRingedSpace ⊤ s).mp hs x hx
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.2 (hdim x)
  have : Subsingleton (PrimeSpectrum (X.presheaf.stalk x)) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum _
  refine isUnit_of_mem_nonZeroDivisors_of_subsingleton_primeSpectrum _
    (mem_nonZeroDivisors_iff.mpr ⟨fun a ha => hreg ?_, fun a ha => hreg ?_⟩)
  all_goals
    change _ • a = _ • (0 : X.presheaf.stalk x)
    simpa only [smul_eq_mul, mul_comm, mul_zero, zero_mul] using ha

/-- **A flat preimmersion from a scheme with zero-dimensional local rings lands in the generic
points.** A flat preimmersion induces isomorphisms on local rings, and a point of a scheme has a
zero-dimensional local ring exactly when it is the generic point of an irreducible component. -/
theorem mem_genericPoints_of_flat_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IsPreimmersion f] (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 0) (x : X) :
    f x ∈ genericPoints Y := by
  refine (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints Y (f x)).mp ?_
  have := isIso_stalkMap_of_flat_isPreimmersion f x
  exact (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.ringKrullDim.trans (hdim x)

/-- **A scheme with zero-dimensional local rings which is a flat preimmersion over a scheme with
finitely many generic points is finite and discrete.** Its points inject into the generic points
of the target, because a flat preimmersion is an isomorphism on local rings and an embedding; and
a point whose local ring is zero-dimensional is maximal for specialization, which makes the space
`T1`, hence discrete once it is finite. -/
theorem finite_and_discreteTopology_of_flat_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [IsPreimmersion f] (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 0)
    (hfinite : (genericPoints Y).Finite) : Finite X ∧ DiscreteTopology X := by
  have : Finite (genericPoints Y) := hfinite
  have : Finite X := Finite.of_injective
    (fun x => (⟨f x, mem_genericPoints_of_flat_isPreimmersion f hdim x⟩ : genericPoints Y))
    (fun x y h => f.isEmbedding.injective (congrArg Subtype.val h))
  have hmax (x : X) : IsMax x := (mem_genericPoints_iff_isMax X x).mp
    ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X x).mp (hdim x))
  have : T1Space X := t1Space_iff_specializes_imp_eq.mpr fun x y hxy =>
    (inseparable_iff_specializes_and.mpr
      ⟨hxy, Scheme.le_iff_specializes.mp (hmax y (Scheme.le_iff_specializes.mpr hxy))⟩).eq
  exact ⟨inferInstance, inferInstance⟩

/-- **The global sections of a discrete scheme are the product of its local rings.** Each point
is an open subset, so the germ maps assemble into a bijection by the sheaf condition for the
cover by singletons. -/
theorem bijective_pi_germ_of_discreteTopology (X : Scheme.{u}) [DiscreteTopology X] :
    Function.Bijective (fun s : Γ(X, ⊤) => fun x : X => X.presheaf.germ ⊤ x trivial s) := by
  classical
  refine ⟨fun s t h => TopCat.Presheaf.section_ext X.sheaf ⊤ s t fun x _ => congrFun h x,
    fun t => ?_⟩
  let V : X → X.Opens := fun x => ⟨{x}, isOpen_discrete _⟩
  have hV (x : X) : x ∈ V x := Set.mem_singleton x
  have hs (x : X) : ∃ s : Γ(X, V x), X.presheaf.germ (V x) x (hV x) s = t x := by
    obtain ⟨U, hxU, s, hs⟩ := X.presheaf.exists_germ_eq (t x)
    exact ⟨X.presheaf.map (homOfLE (Set.singleton_subset_iff.mpr hxU) :
        V x ⟶ U).op s,
      (X.presheaf.germ_res_apply (homOfLE (Set.singleton_subset_iff.mpr hxU) :
        V x ⟶ U) x (hV x) s).trans hs⟩
  choose s hs using hs
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro x y
    rcases eq_or_ne x y with rfl | hxy
    · rfl
    · have he : V x ⊓ V y = ⊥ := by
        ext z
        change (z = x ∧ z = y) ↔ False
        exact ⟨fun h => hxy (h.1.symm.trans h.2), False.elim⟩
      have : Subsingleton Γ(X, V x ⊓ V y) := by
        rw [he]
        infer_instance
      exact Subsingleton.elim _ _
  have hcover : (⊤ : X.Opens) ≤ iSup V := fun x _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hV x⟩
  obtain ⟨g, hg, -⟩ := X.sheaf.existsUnique_gluing' V ⊤
    (fun x => homOfLE le_top) hcover s hcompat
  refine ⟨g, funext fun x => ?_⟩
  change (X.presheaf.germ ⊤ x trivial) g = t x
  calc _ = X.presheaf.germ (V x) x (hV x)
          (X.presheaf.map (homOfLE (show V x ≤ ⊤ from le_top)).op g) :=
        (X.presheaf.germ_res_apply (homOfLE (show V x ≤ ⊤ from le_top)) x (hV x) g).symm
    _ = X.presheaf.germ (V x) x (hV x) (s x) := congrArg _ (hg x)
    _ = t x := hs x

/-- **The global sections of a family of discrete schemes are the product of all their local
rings.** -/
theorem bijective_germ_family_of_discreteTopology {ι : Type*} (X : ι → Scheme.{u})
    [∀ i, DiscreteTopology (X i)] :
    Function.Bijective (fun s : ∀ i, Γ(X i, ⊤) =>
      fun z : Σ i, X i => (X z.1).presheaf.germ ⊤ z.2 trivial (s z.1)) :=
  (Equiv.piCurry (fun i z => (X i).presheaf.stalk z)).symm.bijective.comp
    (Function.Bijective.piMap fun i => bijective_pi_germ_of_discreteTopology (X i))

/-- **The product of the local rings at the generic points of an affine scheme is its total ring
of fractions**, read on the subtype of all generic points rather than on those lying in a given
open.  This is `AlgebraicGeometry.isLocalization_pi_stalk_genericPoints` on the open `⊤`. -/
theorem isLocalization_pi_stalk_genericPoints_top {X : Scheme.{u}} [IsAffine X]
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    letI : ∀ η : genericPoints X, Algebra Γ(X, ⊤) (X.presheaf.stalk η.1) := fun η =>
      X.presheaf.algebra_section_stalk (U := ⊤) ⟨η.1, trivial⟩
    IsLocalization (nonZeroDivisors Γ(X, ⊤)) (∀ η : genericPoints X, X.presheaf.stalk η.1) := by
  let _ : ∀ η : genericPoints X, Algebra Γ(X, ⊤) (X.presheaf.stalk η.1) := fun η =>
    X.presheaf.algebra_section_stalk (U := ⊤) ⟨η.1, trivial⟩
  let _ : ∀ η : {η : genericPoints X // η.1 ∈ (⊤ : X.Opens)},
      Algebra Γ(X, ⊤) (X.presheaf.stalk η.1.1) := fun η =>
    X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
  have := isLocalization_pi_stalk_genericPoints hass hfinite (isAffineOpen_top X)
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors Γ(X, ⊤))
    (show (∀ η : {η : genericPoints X // η.1 ∈ (⊤ : X.Opens)}, X.presheaf.stalk η.1.1) ≃ₐ[Γ(X, ⊤)]
        (∀ η : genericPoints X, X.presheaf.stalk η.1) from
      { toFun := fun s η => s ⟨η, trivial⟩
        invFun := fun s η => s η.1
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl })

/-- **The affine-chart computation.** Let `X` be an affine scheme whose weakly associated points
are generic points of irreducible components and whose quasi-compact opens have finitely many
irreducible components, and let `f i : T i ⟶ X` be a family of flat preimmersions whose points
give exactly the generic points of `X`, each `T i` discrete.  Then the product of the rings of
global sections of the `T i` is the total ring of fractions of `Γ(X, 𝒪)`.

The product of the sections is the product of all the local rings of the `T i`, those local rings
are the local rings of `X` at the corresponding generic points, and the product of the local
rings at the generic points is the total ring of fractions. -/
theorem isLocalization_pi_sections_of_genericPoints {ι : Type*} (X : Scheme.{u}) [IsAffine X]
    (T : ι → Scheme.{u}) (f : ∀ i, T i ⟶ X) [∀ i, Flat (f i)] [∀ i, IsPreimmersion (f i)]
    [∀ i, DiscreteTopology (T i)] (hg : ∀ i (z : T i), f i z ∈ genericPoints X)
    (hb : Function.Bijective (fun z : Σ i, T i => (⟨f z.1 z.2, hg z.1 z.2⟩ : genericPoints X)))
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    letI (i : ι) : Algebra Γ(X, ⊤) Γ(T i, ⊤) := (f i).appTop.hom.toAlgebra
    IsLocalization (nonZeroDivisors Γ(X, ⊤)) (∀ i, Γ(T i, ⊤)) := by
  classical
  let (i : ι) : Algebra Γ(X, ⊤) Γ(T i, ⊤) := (f i).appTop.hom.toAlgebra
  let _ : ∀ η : genericPoints X, Algebra Γ(X, ⊤) (X.presheaf.stalk η.1) := fun η =>
    X.presheaf.algebra_section_stalk (U := ⊤) ⟨η.1, trivial⟩
  have : IsLocalization (nonZeroDivisors Γ(X, ⊤))
      (∀ η : genericPoints X, X.presheaf.stalk η.1) :=
    isLocalization_pi_stalk_genericPoints_top hass hfinite
  let e : (Σ i, T i) ≃ genericPoints X := Equiv.ofBijective _ hb
  let g : (∀ i, Γ(T i, ⊤)) →+* (∀ z : Σ i, T i, (T z.1).presheaf.stalk z.2) :=
    RingHom.pi fun z => ((T z.1).presheaf.germ ⊤ z.2 trivial).hom.comp
      (Pi.evalRingHom (fun i => Γ(T i, ⊤)) z.1)
  let G := RingEquiv.ofBijective g (bijective_germ_family_of_discreteTopology T)
  let a : (∀ η : genericPoints X, X.presheaf.stalk η.1) →+*
      (∀ z : Σ i, T i, (T z.1).presheaf.stalk z.2) :=
    RingHom.pi fun z => ((f z.1).stalkMap z.2).hom.comp
      (Pi.evalRingHom (fun η : genericPoints X => X.presheaf.stalk η.1) (e z))
  have ha : Function.Bijective a := by
    have (z : Σ i, T i) : IsIso ((f z.1).stalkMap z.2) :=
      isIso_stalkMap_of_flat_isPreimmersion (f z.1) z.2
    exact (Function.Bijective.piMap fun z : Σ i, T i =>
      ConcreteCategory.bijective_of_isIso ((f z.1).stalkMap z.2)).comp
        (RingEquiv.piCongrLeft (fun η : genericPoints X => X.presheaf.stalk η.1) e).symm.bijective
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors Γ(X, ⊤))
    { __ := (RingEquiv.ofBijective a ha).trans G.symm
      commutes' := by
        intro r
        refine G.injective ?_
        change G (G.symm (a (algebraMap Γ(X, ⊤) _ r))) = G (algebraMap Γ(X, ⊤) _ r)
        rw [G.apply_symm_apply]
        funext z
        exact (f z.1).germ_stalkMap_apply ⊤ z.2 trivial r }

end AlgebraicGeometry

end
