module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.GeometricStalkReflectsUnits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.SolutionSheafComparisonIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ToposPointPushforward
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk
public import StacksFrontier.CategoryTheory.Sites.Topos.TransportedRingComparisons
public import StacksFrontier.CategoryTheory.Sites.Topos.TransportedSolutionsBijection

/-!
# The hypothesis of step (4) of Stacks 04I6, discharged at every geometric point

`Stacks.EtaleCohomology.isIso_of_forall_bijOn_objSolutions` reduces step (4) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6) — that the comparison
`g⁻¹h_V ⟶ h_W` of sheaves of solutions is an isomorphism — to one hypothesis: at every geometric
point `x̄` of `X`, the coordinatewise map along the stalk of the structure map is a bijection from
the solutions of the system over the stalk of `g⁻¹𝒪_Y` onto its solutions over the stalk of
`𝒪_X`.  This file proves that hypothesis.

`Stacks.Sheaves.PolynomialSystem.bijOn_objSolutions_of_etale` is that bijection, Stacks 04GX over
two transported rings, needing three things of the geometry: that the two transported stalk rings
are strictly henselian local rings, that the stalk functor reflects units for the structure map,
and that the two readings of the coefficients agree.  The last two are hypotheses here — the
second is condition (3) of Stacks 04H9, which
`AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged` supplies for a locally
ringed `(g, g^♯)`, and the third is a property of the chosen coefficient maps.  What is proved
here is the first, for both rings.

For `𝒪_X` it is immediate: `AlgebraicGeometry.etaleStalkRingEquiv` identifies the transported
stalk ring of the structure sheaf at `x̄` with the étale local ring of Stacks 03PS, which is
strictly henselian by Stacks 04HX
(`AlgebraicGeometry.strictlyHenselianLocalRing_etaleLocalRing`), and strict henselianity
transports along a ring isomorphism.  The structure sheaf of commutative rings of the small étale
ringed site has the structure sheaf of Stacks 03DU as its underlying sheaf of rings on the nose,
so the two spellings of the transported ring are the same ring.

For `g⁻¹𝒪_Y` it is the composite of three identifications.  By
`AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiberIso` — the step `q = ȳ` of
the source's proof — there is a geometric point `ȳ` of `Y` with `g⁻¹ ⋙ x̄^{-1} ≅ ȳ^{-1}`.  Along
that isomorphism `CategoryTheory.Sheaf.ringObjEquivOfNatIso` carries the ring transported along
`g⁻¹ ⋙ x̄^{-1}` to the ring transported along `ȳ^{-1}`;
`CategoryTheory.Sheaf.pullbackRingObjEquiv` says the former is the ring transported from `g⁻¹𝒪_Y`
along `x̄^{-1}`; and `AlgebraicGeometry.etaleStalkRingEquiv` at `ȳ` identifies the latter with the
étale local ring of `Y` at `ȳ`.  This is the source's sentence that the stalk of `g⁻¹𝒪_Y` at `p`
is the strictly henselian local ring `𝒪_{Y,ȳ}`.

With that hypothesis available at every geometric point, step (4) itself follows:
`Stacks.EtaleCohomology.isIso_inverseImageForkComparison` says the comparison morphism of step
(3) is an isomorphism, with no hypothesis left beyond the fork data of steps (1)–(3), the
compatibility of the two readings of the coefficients, and reflection of units for the structure
map.

No `@[stacks 04I6]` tag is registered: 04I6 asserts the existence and uniqueness of a morphism of
schemes `f : X ⟶ Y` together with a 2-isomorphism `(g, g^♯) ≅ (f_small, f_small^♯)`, and what is
proved here is one of the seven steps of its proof — the 2-isomorphism itself, and the morphism
`f`, are still to be assembled.

## Main results

* `AlgebraicGeometry.strictlyHenselianLocalRing_objCommRing_structureSheaf`: **the transported
  stalk ring of the structure sheaf at a geometric point is strictly henselian.**
* `AlgebraicGeometry.strictlyHenselianLocalRing_objCommRing_inverseImageStructureSheaf`: **the
  transported stalk ring of the inverse image of the structure sheaf of `Y` at a geometric point
  of `X` is strictly henselian.**
* `Stacks.EtaleCohomology.bijOn_objSolutions_geometricPoint`: **the hypothesis of
  `Stacks.EtaleCohomology.isIso_of_forall_bijOn_objSolutions`**, at one geometric point.
* `Stacks.EtaleCohomology.isIso_inverseImageForkComparison`: **step (4) of the proof of
  Stacks 04I6**, the comparison of sheaves of solutions is an isomorphism.

## References

* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.PolynomialSystem
open scoped CommRingObj Obj

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.sheafCommRingObj CategoryTheory.Sheaf.ringObjRing

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) {Y : Scheme.{u}}
  (hY : B.Contains Y)

/-- **The transported stalk ring of the structure sheaf at a geometric point is a strictly
henselian local ring.**

The stalk functor of the point of the small étale site attached to a geometric point `x̄` carries
the underlying sheaf of sets of the structure sheaf of commutative rings to a set with a
transported ring structure, and `AlgebraicGeometry.etaleStalkRingEquiv` identifies that ring with
the étale local ring of Stacks 03PS at `x̄`, which is strictly henselian by Stacks 04HX.  Strict
henselianity transports along a ring isomorphism
(`StrictlyHenselianLocalRing.of_ringEquiv`). -/
theorem strictlyHenselianLocalRing_objCommRing_structureSheaf (s : GeometricPoint X) :
    letI := objCommRing (SmallEtale.commRingStructureSheaf B X hX)
      ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u))
    StrictlyHenselianLocalRing (((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)).obj
      (Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
        (SmallEtale.commRingStructureSheaf B X hX))) := by
  let := objCommRing (SmallEtale.commRingStructureSheaf B X hX)
    ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u))
  exact StrictlyHenselianLocalRing.of_ringEquiv (etaleStalkRingEquiv B X hX s).symm

variable (f : MorphismOfTopoi (Sheaf (SmallEtale.topology B X hX) (Type u))
  (Sheaf (SmallEtale.topology B Y hY) (Type u)))

/-- **The transported stalk ring of the inverse image of the structure sheaf of `Y` at a
geometric point of `X` is a strictly henselian local ring.**

This is the sentence of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6) that the stalk of `g⁻¹𝒪_Y` at the point
`p` of `Sh(X_étale)` is `𝒪_{Y,ȳ}`, where `ȳ` is the geometric point of `Y` that `g` and `x̄`
determine.

Three identifications compose.  `CategoryTheory.Sheaf.pullbackRingObjEquiv` replaces the ring
transported from `g⁻¹𝒪_Y` along the stalk functor at `x̄` by the ring transported from `𝒪_Y`
along `g⁻¹` followed by that stalk functor — the same operations on the same type.
`AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiberIso` produces `ȳ` together
with an isomorphism of that composite functor with the stalk functor at `ȳ`, along which
`CategoryTheory.Sheaf.ringObjEquivOfNatIso` carries the ring transported along the composite to
the ring transported along the stalk functor at `ȳ`.  Finally
`AlgebraicGeometry.etaleStalkRingEquiv` identifies that with the étale local ring of `Y` at `ȳ`,
which is strictly henselian by Stacks 04HX. -/
theorem strictlyHenselianLocalRing_objCommRing_inverseImageStructureSheaf
    (s : GeometricPoint X) :
    letI := objCommRing (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
      (SmallEtale.topology B X hX) f.inverseImage
      (SmallEtale.commRingStructureSheaf B Y hY))
      ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u))
    StrictlyHenselianLocalRing (((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)).obj
      (Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
        (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
          (SmallEtale.topology B X hX) f.inverseImage
          (SmallEtale.commRingStructureSheaf B Y hY)))) := by
  let := objCommRing (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
    (SmallEtale.topology B X hX) f.inverseImage
    (SmallEtale.commRingStructureSheaf B Y hY))
    ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u))
  obtain ⟨y, ⟨e⟩⟩ := exists_geometricPoint_inverseImage_comp_sheafFiberIso B hX hY f s
  exact StrictlyHenselianLocalRing.of_ringEquiv
    (((CategoryTheory.Sheaf.pullbackRingObjEquiv (SmallEtale.topology B X hX)
          f.inverseImage (SmallEtale.structureSheaf B Y hY)
          ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u))).trans
        (CategoryTheory.Sheaf.ringObjEquivOfNatIso (SmallEtale.structureSheaf B Y hY) e)).trans
      (etaleStalkRingEquiv B Y hY y)).symm

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open AlgebraicGeometry AlgebraicGeometry.RingedTopos

attribute [local instance] Stacks.sheafCommRingObj
  Stacks.Sheaves.PolynomialSystem.objCommRing

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) {Y : Scheme.{u}}
  (hY : B.Contains Y)
  (f : MorphismOfTopoi (Sheaf (SmallEtale.topology B X hX) (Type u))
    (Sheaf (SmallEtale.topology B Y hY) (Type u)))

/-- **The hypothesis of step (4) of the proof of
[Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6), at one geometric point.**

Let `g : Sh(X_étale) ⟶ Sh(Y_étale)` be a morphism of topoi, let
`α : g⁻¹𝒪_Y ⟶ 𝒪_X` be a morphism of sheaves of commutative rings, let
`P₁, …, P_n ∈ Γ[x₁, …, x_n]` present an étale `Γ`-algebra, and let `c₁` and `c'` read the
coefficients into the global sections of `g⁻¹𝒪_Y` and of `𝒪_X` compatibly along `α`.  Suppose the
stalk functor at a geometric point `x̄` of `X` reflects units for `α` — condition (3) of
Stacks 04H9, which `AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged` gives
whenever `(g, g^♯)` is a morphism of *locally* ringed topoi.  Then the coordinatewise map along
the stalk of `α` is a bijection from the solutions of the system over the stalk of `g⁻¹𝒪_Y` onto
its solutions over the stalk of `𝒪_X`.

This is exactly the hypothesis `hbij` of
`Stacks.EtaleCohomology.isIso_of_forall_bijOn_objSolutions`, at one point.  It is
`Stacks.Sheaves.PolynomialSystem.bijOn_objSolutions_of_etale`, which is Stacks 04GX over the two
transported rings, with the strict henselianity of those rings supplied by
`AlgebraicGeometry.strictlyHenselianLocalRing_objCommRing_inverseImageStructureSheaf` and
`AlgebraicGeometry.strictlyHenselianLocalRing_objCommRing_structureSheaf`. -/
theorem bijOn_objSolutions_geometricPoint
    (α : pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
        (SmallEtale.topology B X hX) f.inverseImage
        (SmallEtale.commRingStructureSheaf B Y hY) ⟶
      SmallEtale.commRingStructureSheaf B X hX)
    {Γ : Type*} [CommRing Γ] {n : ℕ} (P : Fin n → MvPolynomial (Fin n) Γ)
    [Algebra.Etale Γ (MvPolynomial (Fin n) Γ ⧸ Ideal.span (Set.range P))]
    (c₁ : Γ →+* (𝟙_ (Sheaf (SmallEtale.topology B X hX) (Type u)) ⟶
      Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
        (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
          (SmallEtale.topology B X hX) f.inverseImage
          (SmallEtale.commRingStructureSheaf B Y hY))))
    (c' : Γ →+* (𝟙_ (Sheaf (SmallEtale.topology B X hX) (Type u)) ⟶
      Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
        (SmallEtale.commRingStructureSheaf B X hX)))
    (hc' : ∀ r, c' r = c₁ r ≫ underlyingMap α)
    (s : GeometricPoint X)
    (hu : ReflectsUnitsObj ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)) α) :
    Set.BijOn
      (fun a : Fin n → ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)).obj
          (Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
            (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
              (SmallEtale.topology B X hX) f.inverseImage
              (SmallEtale.commRingStructureSheaf B Y hY))) =>
        fun i => ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)).map
          (underlyingMap α) (a i))
      (objSolutions ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)) (Fin n) P
        (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
          (SmallEtale.topology B X hX) f.inverseImage
          (SmallEtale.commRingStructureSheaf B Y hY)) c₁)
      (objSolutions ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)) (Fin n) P
        (SmallEtale.commRingStructureSheaf B X hX) c') := by
  have := strictlyHenselianLocalRing_objCommRing_inverseImageStructureSheaf B hX hY f s
  have := strictlyHenselianLocalRing_objCommRing_structureSheaf B hX s
  refine bijOn_objSolutions_of_etale _ _ _ α P c₁ c' hu fun r => ?_
  refine (map_objGlobalRingHom _ α (c₁ r)).trans ?_
  rw [hc' r]

/-- **Step (4) of the proof of [Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6): the
comparison of sheaves of solutions is an isomorphism.**

Let `g : Sh(X_étale) ⟶ Sh(Y_étale)` be a morphism of topoi and `α : g⁻¹𝒪_Y ⟶ 𝒪_X` a morphism of
sheaves of commutative rings whose stalk functors reflect units — which they do at every
geometric point when `(g, g^♯)` is a morphism of *locally* ringed topoi, by Stacks 04H9
(`AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged`).  Let
`P₁, …, P_n ∈ Γ[x₁, …, x_n]` present an étale `Γ`-algebra, let the solutions of the system over
`𝒪_Y` be cut out by a limit fork with coordinates `ι` and the solutions of the pushed system over
`𝒪_X` by a limit fork with coordinates `ι'`, and let the coefficients be read compatibly.  Then
the comparison morphism `Stacks.Sheaves.inverseImageForkComparison` of step (3) is an
isomorphism.

This is `Stacks.EtaleCohomology.isIso_of_forall_bijOn_objSolutions` — the source's reduction to
the geometric points, through the conservativity of Stacks 021B — fed at every geometric point
with `Stacks.EtaleCohomology.bijOn_objSolutions_geometricPoint`, which is Stacks 04GX over the
two strictly henselian stalk rings.  The compatibility of the readings of the coefficients at a
point is `Stacks.Sheaves.PolynomialSystem.map_objGlobalRingHom`.

In the source's notation `H = h_V` for an affine `V = Spec(C)` étale over `Y = Spec(B)` with the
standard presentation `C = B[x₁, …, x_n]/(P₁, …, P_n)`, and the fork upstairs cuts out
`h_{X ×_Y V}`; the conclusion is that `g⁻¹h_V ⟶ h_{X ×_Y V}` is an isomorphism. -/
theorem isIso_inverseImageForkComparison
    (α : pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
        (SmallEtale.topology B X hX) f.inverseImage
        (SmallEtale.commRingStructureSheaf B Y hY) ⟶
      SmallEtale.commRingStructureSheaf B X hX)
    {Γ : Type*} [CommRing Γ] {n : ℕ} (P : Fin n → MvPolynomial (Fin n) Γ)
    [Algebra.Etale Γ (MvPolynomial (Fin n) Γ ⧸ Ideal.span (Set.range P))]
    {H : Sheaf (SmallEtale.topology B Y hY) (Type u)}
    (ι : H ⟶ ∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf (SmallEtale.topology B Y hY)
      (SmallEtale.commRingStructureSheaf B Y hY))
    (c : Γ →+* (𝟙_ (Sheaf (SmallEtale.topology B Y hY) (Type u)) ⟶
      Stacks.underlyingRingSheaf (SmallEtale.topology B Y hY)
        (SmallEtale.commRingStructureSheaf B Y hY)))
    (c₁ : Γ →+* (𝟙_ (Sheaf (SmallEtale.topology B X hX) (Type u)) ⟶
      Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
        (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
          (SmallEtale.topology B X hX) f.inverseImage
          (SmallEtale.commRingStructureSheaf B Y hY))))
    (hc₁ : ∀ r, c₁ r = Functor.LaxMonoidal.ε f.inverseImage ≫ f.inverseImage.map (c r))
    (c' : Γ →+* (𝟙_ (Sheaf (SmallEtale.topology B X hX) (Type u)) ⟶
      Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
        (SmallEtale.commRingStructureSheaf B X hX)))
    (hc' : ∀ r, c' r = c₁ r ≫ underlyingMap α)
    (hι : ι ≫ CommRingObj.evalSystemHom
        (Stacks.underlyingRingSheaf (SmallEtale.topology B Y hY)
          (SmallEtale.commRingStructureSheaf B Y hY)) c (Fin n) P =
      ι ≫ CommRingObj.zeroSystemHom
        (Stacks.underlyingRingSheaf (SmallEtale.topology B Y hY)
          (SmallEtale.commRingStructureSheaf B Y hY)) (Fin n) (Fin n))
    (hs : IsLimit (Fork.ofι ι hι))
    {T : Sheaf (SmallEtale.topology B X hX) (Type u)}
    {ι' : T ⟶ ∏ᶜ fun _ : Fin n => Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
      (SmallEtale.commRingStructureSheaf B X hX)}
    (h' : ι' ≫ CommRingObj.evalSystemHom
        (Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
          (SmallEtale.commRingStructureSheaf B X hX)) c' (Fin n) P =
      ι' ≫ CommRingObj.zeroSystemHom
        (Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
          (SmallEtale.commRingStructureSheaf B X hX)) (Fin n) (Fin n))
    (hl' : IsLimit (Fork.ofι ι' h'))
    (hu : ∀ s : GeometricPoint X,
      ReflectsUnitsObj ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)) α) :
    IsIso (Stacks.Sheaves.inverseImageForkComparison f
      (SmallEtale.commRingStructureSheaf B Y hY) α (Fin n) ι c c₁ hc₁ c' hc' P hl' hι) :=
  isIso_of_forall_bijOn_objSolutions B hX hY f (SmallEtale.commRingStructureSheaf B Y hY)
    (Fin n) ι c c₁ hc₁ α c' P hι hs h' hl' _
    (Stacks.Sheaves.inverseImageForkComparison_comp_ι f
      (SmallEtale.commRingStructureSheaf B Y hY) α (Fin n) ι c c₁ hc₁ c' hc' P hl' hι)
    fun s => bijOn_objSolutions_geometricPoint B hX hY f α P c₁ c' hc' s (hu s)

end Stacks.EtaleCohomology

end
