module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorStalkResidueCokernel
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierWeilDivisor
public import
  StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalCycleMultiplicity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.AtPointCriteria
public import StacksFrontier.RingTheory.OrderOfVanishing.ResidualCokernel

/-!
# Multiplicity one from étaleness

Let `f : X ⟶ S` be a morphism of schemes which is étale at a point `ξ` of `X`, and let `η = f ξ`.
Extending the maximal ideal of `𝒪_{S, η}` along the stalk map gives the maximal ideal of
`𝒪_{X, ξ}`, so any ideal of `𝒪_{X, ξ}` which contains that extension and is not the unit ideal
is the maximal ideal, and the quotient by it has length one.

Geometrically: `η` is the generic point of an integral closed subscheme `Z' ⊆ S`, so the ideal
of `Z'` in `𝒪_{S, η}` *is* the maximal ideal there; a closed subscheme of `X` which is contained
in `f^{-1}(Z')` and passes through `ξ` therefore has length-one local ring at `ξ`. This is the
step the proof of Stacks 0B0E marks "local calculation omitted": with `π : X → 𝐏(V_n)` étale at a
point of `Z`, the closed subscheme `C ∩ X = π^{-1}(π(Z))` contains `Z` with multiplicity one, and
that multiplicity-one hypothesis is what the local form of Stacks 0B1J consumes.

## Main results

* `AlgebraicGeometry.TorFormula.maximalIdeal_le_sup_of_surjective`: a containment of the maximal
  ideal descends through a surjection of local rings, modulo an ideal containing its kernel.
* `AlgebraicGeometry.TorFormula.length_quotient_eq_one_of_maximalIdeal_le`: the length-one
  criterion for a quotient of a local ring.
* `AlgebraicGeometry.TorFormula.sup_localIdealAt_ne_top`: the sum of the local ideals of two
  closed subvarieties through a point is not the unit ideal.
* `AlgebraicGeometry.TorFormula.localIdealAt_self_eq_maximalIdeal`: the local ideal of the
  reduced closure of a point, read at that point itself, is the maximal ideal.
* `AlgebraicGeometry.TorFormula.map_maximalIdeal_stalkMap_eq_of_etaleAt`: at a point where a
  morphism locally of finite presentation is étale, the extension of the maximal ideal of the
  base along the stalk map is the maximal ideal.
* `AlgebraicGeometry.TorFormula.length_quotient_eq_one_of_etaleAt`: the multiplicity-one
  computation for an arbitrary proper ideal containing that extension.
* `AlgebraicGeometry.TorFormula.length_quotient_sup_localIdealAt_eq_one_of_etaleAt`: the same in
  the shape the local form of Stacks 0B1J takes as its transversality hypothesis, for the sum of
  the local ideals of two closed subvarieties through `ξ`.
* `TorFormula.length_quotient_sup_localIdealAt_eq_one_of_etaleAt_closedSubscheme`: the same on an
  *ambient* scheme, with the étale morphism defined only on a closed subscheme through the point.
  This is the shape the proof of Stacks 0B0E needs, the projection there being étale on the
  nonsingular subvariety and nowhere on the projective space containing it.

## Implementation notes

The pointwise statement about the maximal ideal is read off the criteria of Tag 02GU, whose
seventh item is flatness of the stalk map together with exactly that identity and the finite
separability of the residue-field extension; it needs the morphism to be locally of finite
presentation, which is how that tag is stated. The global version for a morphism all of whose
fibres are étale is `AlgebraicGeometry.map_maximalIdeal_eq_of_etale_fibers`, and neither is a
consequence of the other: this one is pointwise but asks for finite presentation.

The hypothesis of `length_quotient_eq_one_of_etaleAt` is written as a containment of the
*extension of the local ideal of the reduced closure of `f ξ`* rather than of the maximal ideal,
which is the same ideal by `localIdealAt_self_eq_maximalIdeal` and is the form in which the
geometry supplies it: the ideal of the closed subscheme `f^{-1}(closure {f ξ})` at `ξ` is the
extension of the ideal of `closure {f ξ}` at `f ξ`, and the containment says that the closed
subscheme whose ideal is `I` lies inside `f^{-1}(closure {f ξ})`.

That the ideal is not the unit ideal is the statement that `ξ` lies on the closed subscheme it
cuts out; in the two-subvariety form it is supplied by `ξ` lying in the closures of both points.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1J](https://stacks.math.columbia.edu/tag/0B1J)
* [Stacks Project, Tag 02GU](https://stacks.math.columbia.edu/tag/02GU)
* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.TorFormula

variable {X S : Scheme.{u}}

/-! ### The length-one criterion -/

/-- **Descending a containment of the maximal ideal through a surjection.** Let `φ : A ↠ B` be a
surjection of local rings, let `I` and `J` be ideals of `A` with `ker φ ≤ J`, and suppose the
extension of `I` to `B` contains the maximal ideal of `B`. Then `I ⊔ J` contains the maximal
ideal of `A`.

Given `a` in the maximal ideal of `A`, its image lies in `Ideal.map φ I`, hence agrees with the
image of some element of `I`; the difference lies in `ker φ ≤ J`. -/
public theorem maximalIdeal_le_sup_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) (hφ : Function.Surjective φ) {I J : Ideal A}
    (hJ : RingHom.ker φ ≤ J) (hI : IsLocalRing.maximalIdeal B ≤ Ideal.map φ I) :
    IsLocalRing.maximalIdeal A ≤ I ⊔ J := by
  have _ : IsLocalHom φ := IsLocalHom.of_surjective φ hφ
  calc IsLocalRing.maximalIdeal A = Ideal.comap φ (IsLocalRing.maximalIdeal B) :=
        (IsLocalRing.maximalIdeal_comap φ).symm
    _ ≤ Ideal.comap φ (Ideal.map φ I) := Ideal.comap_mono hI
    _ = I ⊔ RingHom.ker φ := Ideal.comap_map_of_surjective φ hφ I
    _ ≤ I ⊔ J := sup_le_sup_left hJ I

/-- An ideal of a local ring which contains the maximal ideal and is not the unit ideal *is* the
maximal ideal, so the quotient by it is the residue field and has length one. -/
public theorem length_quotient_eq_one_of_maximalIdeal_le {A : Type*} [CommRing A] [IsLocalRing A]
    {I : Ideal A} (hle : IsLocalRing.maximalIdeal A ≤ I) (hne : I ≠ ⊤) :
    Module.length A (A ⧸ I) = 1 := by
  have h : IsLocalRing.maximalIdeal A = I :=
    (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le hne hle
  have hI : I.IsMaximal := h ▸ IsLocalRing.maximalIdeal.isMaximal A
  have : IsSimpleModule A (A ⧸ I) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨I, hI, ⟨LinearEquiv.refl A (A ⧸ I)⟩⟩
  exact Module.length_eq_one A (A ⧸ I)

/-! ### The ideal of a closed subvariety at its own generic point -/

/-- **The local ideal of the reduced closure of a point, at that point itself, is the maximal
ideal.** The reduced closure of `x` is an integral closed subscheme with generic point `x`, and
the local ring of an integral closed subscheme at its generic point is the residue field of the
ambient local ring there. -/
public theorem localIdealAt_self_eq_maximalIdeal (x : X) :
    localIdealAt x x = IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have hint : IsIntegral (Stacks.Chow.integralComponentAt x).subscheme :=
    Stacks.Chow.isIntegral_integralComponentAt x
  have hgen : (Stacks.Chow.integralComponentAt x).subschemeι.base
      (genericPoint ((Stacks.Chow.integralComponentAt x).subscheme : Type u)) = x :=
    Stacks.Chow.genericPointOf_integralComponentAt x
  have h := IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal
    (Stacks.Chow.integralComponentAt x)
  rw [hgen] at h
  exact h

/-- **The sum of the local ideals of two closed subvarieties through a point is not the unit
ideal.** Each is contained in the maximal ideal there, because the point lies on the subvariety,
and the maximal ideal is proper. -/
public theorem sup_localIdealAt_ne_top {c y ξ : X} (hξc : ξ ∈ closure ({c} : Set X))
    (hξy : ξ ∈ closure ({y} : Set X)) : localIdealAt c ξ ⊔ localIdealAt y ξ ≠ ⊤ := by
  have h : ∀ {z : X}, ξ ∈ closure {z} →
      localIdealAt z ξ ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := fun hz =>
    (IdealSheafData.stalk_le_maximalIdeal_iff_mem_support _ ξ).mpr
      (mem_support_integralComponentAt hz)
  exact fun htop => (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk ξ)).ne_top
    (top_le_iff.mp (htop ▸ sup_le (h hξc) (h hξy)))

/-! ### The maximal ideal at a point of étaleness -/

/-- **At a point where a morphism locally of finite presentation is étale, the extension of the
maximal ideal of the base along the stalk map is the maximal ideal.** This is the seventh item
of the criteria of Tag 02GU, read in one direction. -/
public theorem map_maximalIdeal_stalkMap_eq_of_etaleAt (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) (hf : EtaleAt f x) :
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have htfae := (etaleAt_tfae f x).out 1 7
  obtain ⟨-, h, -⟩ := htfae.mp hf
  exact h

/-! ### Multiplicity one -/

/-- **Multiplicity one from étaleness.** Let `f : X ⟶ S` be locally of finite presentation and
étale at `ξ`, and let `I` be an ideal of `𝒪_{X, ξ}` which contains the extension of the ideal of
the reduced closure of `f ξ` and is not the unit ideal. Then `𝒪_{X, ξ} ⧸ I` has length one.

Geometrically, the closed subscheme cut out by `I` passes through `ξ` and is contained in
`f^{-1}(closure {f ξ})`; since `f` is étale at `ξ`, that preimage already has length-one local
ring there, so the smaller subscheme does too. -/
public theorem length_quotient_eq_one_of_etaleAt (f : X ⟶ S)
    [LocallyOfFinitePresentation f] {ξ : X} (hf : EtaleAt f ξ)
    {I : Ideal (X.presheaf.stalk ξ)}
    (hle : Ideal.map (f.stalkMap ξ).hom (localIdealAt (f ξ) (f ξ)) ≤ I)
    (hne : I ≠ ⊤) :
    Module.length (X.presheaf.stalk ξ) (X.presheaf.stalk ξ ⧸ I) = 1 := by
  refine length_quotient_eq_one_of_maximalIdeal_le ?_ hne
  rw [← map_maximalIdeal_stalkMap_eq_of_etaleAt f ξ hf]
  rwa [localIdealAt_self_eq_maximalIdeal] at hle

/-- **Multiplicity one from étaleness, in the shape Stacks 0B1J consumes.** Let `f : X ⟶ S` be
locally of finite presentation and étale at `ξ`, let `c` and `y` be points of `X` whose closures
both contain `ξ`, and suppose the scheme-theoretic intersection of their reduced closures lies
inside `f^{-1}(closure {f ξ})` at `ξ`. Then

`length_{𝒪_{X, ξ}} (𝒪_{X, ξ} ⧸ (I ⊔ J)) = 1`

for `I` and `J` the local ideals of the two closed subvarieties at `ξ`, which is the
transversality hypothesis of the local form of Stacks 0B1J. -/
public theorem length_quotient_sup_localIdealAt_eq_one_of_etaleAt (f : X ⟶ S)
    [LocallyOfFinitePresentation f] {ξ : X} (hf : EtaleAt f ξ) {c y : X}
    (hξc : ξ ∈ closure ({c} : Set X)) (hξy : ξ ∈ closure ({y} : Set X))
    (hle : Ideal.map (f.stalkMap ξ).hom (localIdealAt (f ξ) (f ξ)) ≤
      localIdealAt c ξ ⊔ localIdealAt y ξ) :
    Module.length (X.presheaf.stalk ξ)
      (X.presheaf.stalk ξ ⧸ (localIdealAt c ξ ⊔ localIdealAt y ξ)) = 1 :=
  length_quotient_eq_one_of_etaleAt f hf hle (sup_localIdealAt_ne_top hξc hξy)

/-! ### Étaleness along a closed subscheme -/

/-- **Multiplicity one on the ambient scheme, from étaleness along a closed subscheme through the
point.** Let `i : X ⟶ P` be surjective on stalks — a closed immersion, say — let `π : X ⟶ S` be
locally of finite presentation and étale at a point `ζ` of `X`, and let `c` and `y` be points of
`P` whose closures contain `i ζ`. Suppose

* the kernel of the stalk map of `i` at `ζ`, which is the ideal of `X` in `P` there, is contained
  in the local ideal of the reduced closure of `y`, and
* the ideal cut out on `X` by `π^{-1}(closure {π ζ})` at `ζ` is contained in the ideal cut out
  there by the reduced closure of `c`.

Then `𝒪_{P, i ζ} ⧸ (I_c ⊔ I_y)` has length one, which is the transversality hypothesis of the
local form of Stacks 0B1J on the *ambient* scheme `P`.

This is the form the proof of Stacks 0B0E needs. There `P = 𝐏^N`, `X` is the nonsingular closed
subvariety, `c` is the generic point of the cone `C` and `y` that of `X`, and the étale morphism
is the projection `π = (r_{n+1} ∘ ⋯ ∘ r_N)|_X` — a morphism of `X`, not of `𝐏^N`, on which the
projection is an `𝔸^{N-n}`-bundle and so étale nowhere. The second hypothesis is the identity
`C ∩ X = π^{-1}(π(Z))`, and no compatibility of the intersection product with restriction to an
open subscheme is involved: the descent is along the surjection of local rings alone. -/
public theorem length_quotient_sup_localIdealAt_eq_one_of_etaleAt_closedSubscheme
    {P : Scheme.{u}} (i : X ⟶ P) [SurjectiveOnStalks i] (π : X ⟶ S)
    [LocallyOfFinitePresentation π] {ζ : X} (hπ : EtaleAt π ζ) {c y : P}
    (hξc : i.base ζ ∈ closure ({c} : Set P)) (hξy : i.base ζ ∈ closure ({y} : Set P))
    (hJ : RingHom.ker (i.stalkMap ζ).hom ≤ localIdealAt y (i.base ζ))
    (hI : Ideal.map (π.stalkMap ζ).hom (localIdealAt (π.base ζ) (π.base ζ)) ≤
      Ideal.map (i.stalkMap ζ).hom (localIdealAt c (i.base ζ))) :
    Module.length (P.presheaf.stalk (i.base ζ))
      (P.presheaf.stalk (i.base ζ) ⧸
        (localIdealAt c (i.base ζ) ⊔ localIdealAt y (i.base ζ))) = 1 := by
  refine length_quotient_eq_one_of_maximalIdeal_le ?_ (sup_localIdealAt_ne_top hξc hξy)
  refine maximalIdeal_le_sup_of_surjective (i.stalkMap ζ).hom (i.stalkMap_surjective ζ) hJ ?_
  rw [← map_maximalIdeal_stalkMap_eq_of_etaleAt π ζ hπ,
    ← localIdealAt_self_eq_maximalIdeal (π.base ζ)]
  exact hI

end AlgebraicGeometry.TorFormula

end
