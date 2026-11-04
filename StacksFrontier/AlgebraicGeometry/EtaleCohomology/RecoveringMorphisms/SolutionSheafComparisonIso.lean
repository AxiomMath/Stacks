module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.StalkReflectsUnits
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.ToposHomUnitsSquare
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing
public import StacksFrontier.CategoryTheory.Sites.Topos.InverseImageSolutionStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Step (4) of Stacks 04I6: the comparison of sheaves of solutions is an isomorphism

Let `(g, g^♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of ringed topoi between
the small étale ringed topoi of two schemes of a big étale site, let `V` be an affine object of
the small étale site of `Y` presented by a polynomial system `P` over `Γ(Y, ⊤)`, and let `W` be
the corresponding chart upstairs.  Step (3) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6) produces the comparison
`g⁻¹h_V ⟶ h_W`; step (4) asserts that it is an isomorphism.  The source's argument is: the small
étale site has enough points, so it suffices to check bijectivity on stalks, and on stalks the
map is the bijection of
[Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX) between the solutions of
an étale system over two strictly henselian local rings along a local homomorphism.

This file supplies the two halves of that argument that are not ring theory.

The first is the reduction itself,
`Stacks.EtaleCohomology.isIso_of_forall_bijOn_objSolutions`: the comparison is an isomorphism as
soon as, at every geometric point of `X`, the coordinatewise map along the stalk of `g^♯` is a
bijection from the solutions of `P` over the stalk of `g⁻¹𝒪_Y` onto the solutions of `P` over
the stalk of `𝒪_X`.  It is `AlgebraicGeometry.isIso_iff_forall_bijective_sheafFiber`, the
conservativity of the geometric points of Stacks 021B, fed with
`Stacks.Sheaves.bijective_map_of_comp_forkι`, which identifies the two stalks with the two
solution sets.

The second is the hypothesis of Stacks 04H9 that the ring-theoretic half needs,
`AlgebraicGeometry.isLocalHom_sheafFiber_fSharpInverseImage`: for a *locally* ringed `(g, g^♯)`
the stalk of `g^♯` at a geometric point of `X` is a **local** homomorphism.  This is the sentence
"since `(g, g^♯)` is a morphism of locally ringed topoi we see that `(g^♯)_p` is a local
homomorphism of local rings" of the source's proof.  It is Stacks 04H9 (1) ⇒ (3) for a morphism
of ringed topoi, `AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged`, read at
a stalk functor and then turned into locality by
`AlgebraicGeometry.RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj`.

What is **not** here is the ring theory: that the two stalks are strictly henselian local rings
and that the coordinatewise map between the solution sets is bijective, which is Stacks 04GX
(`bijOn_solutions_of_etale`) transported along
`AlgebraicGeometry.etaleStalkRingEquiv`.  So no declaration here proves a clause of
Stacks 04I6 and none carries an `@[stacks 04I6]` tag; that tag asserts the existence and
uniqueness of a morphism of schemes `f : X ⟶ Y` together with a 2-isomorphism
`(g, g^♯) ≅ (f_small, f_small^♯)`.

## Main results

* `AlgebraicGeometry.isLocalHom_sheafFiber_fSharpInverseImage`: **the stalk of `g^♯` at a
  geometric point is a local homomorphism**, for a locally ringed morphism of small étale ringed
  topoi.
* `Stacks.EtaleCohomology.isIso_of_forall_bijOn_objSolutions`: **the comparison of sheaves of
  solutions is an isomorphism** as soon as it is a bijection of solution sets at every geometric
  point.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Stacks.Sheaves.ToposPullback
open scoped CommRingObj Obj

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}

/-- **The stalk of `g^♯` at a geometric point is a local homomorphism of local rings.**

Let `(g, g^♯)` be a morphism of ringed topoi between the small étale ringed topoi of two schemes
of a big étale site, and suppose it is a morphism of *locally* ringed topoi.  Then at every
geometric point `x̄` of `X` the induced map of stalks `(g⁻¹𝒪_Y)_x̄ ⟶ (𝒪_X)_x̄`, taken in
commutative rings, is a local ring homomorphism.

This is the sentence "since `(g, g^♯)` is a morphism of locally ringed topoi we see that
`(g^♯)_p` is a local homomorphism of local rings" of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6), and it is Stacks 04H9
(1) ⇒ (3) at a stalk functor: a locally ringed morphism of ringed topoi has units reflected by
every left exact functor to sets
(`AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged`), and at a stalk functor
reflection of units is locality of the stalk map
(`AlgebraicGeometry.RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj`). -/
@[sga "4 IV 13.9" "(i) ⇒ (ii), special case"]
theorem isLocalHom_sheafFiber_fSharpInverseImage
    (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (hg : g.IsLocallyRinged) (s : GeometricPoint X.obj) :
    IsLocalHom ((geometricPointSitePoint B X.obj X.property s).sheafFiber
      (A := CommRingCat.{u}) |>.map g.fSharpInverseImage).hom :=
  RingedTopos.isLocalHom_sheafFiber_of_reflectsUnitsObj
    (geometricPointSitePoint B X.obj X.property s) g.fSharpInverseImage
    (g.reflectsUnitsObj_of_isLocallyRinged hg _)

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open AlgebraicGeometry Stacks.Sheaves

attribute [local instance] Stacks.sheafCommRingObj

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) {Y : Scheme.{u}}
  (hY : B.Contains Y)
  (f : MorphismOfTopoi (Sheaf (SmallEtale.topology B X hX) (Type u))
    (Sheaf (SmallEtale.topology B Y hY) (Type u)))
  (O : Sheaf (SmallEtale.topology B Y hY) CommRingCat.{u})
  {Γ : Type*} [CommRing Γ] (κ : Type) [Finite κ] {ν : Type} [Finite ν]
  {H : Sheaf (SmallEtale.topology B Y hY) (Type u)}
  (ι : H ⟶ ∏ᶜ fun _ : κ => Stacks.underlyingRingSheaf (SmallEtale.topology B Y hY) O)
  (c : Γ →+* (𝟙_ (Sheaf (SmallEtale.topology B Y hY) (Type u)) ⟶
    Stacks.underlyingRingSheaf (SmallEtale.topology B Y hY) O))
  (c₁ : Γ →+* (𝟙_ (Sheaf (SmallEtale.topology B X hX) (Type u)) ⟶
    Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
      (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
      (SmallEtale.topology B X hX) f.inverseImage O)))
  (hc₁ : ∀ r, c₁ r = Functor.LaxMonoidal.ε f.inverseImage ≫ f.inverseImage.map (c r))
  {O' : Sheaf (SmallEtale.topology B X hX) CommRingCat.{u}}
  (α : pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
      (SmallEtale.topology B X hX) f.inverseImage O ⟶ O')
  (c' : Γ →+* (𝟙_ (Sheaf (SmallEtale.topology B X hX) (Type u)) ⟶
    Stacks.underlyingRingSheaf (SmallEtale.topology B X hX) O'))
  (P : ν → MvPolynomial κ Γ)

include hc₁ in
/-- **Step (4) of the proof of [Stacks 04I6](https://stacks.math.columbia.edu/tag/04I6): the
comparison of sheaves of solutions is an isomorphism.**

Let `H` be the equalizer of the row of a polynomial system `P` over a sheaf of commutative rings
`𝒪` on the small étale site of `Y`, let `T` be the equalizer of the row of the same `P` over a
sheaf of commutative rings `𝒪'` on the small étale site of `X`, and let `m : g⁻¹H ⟶ T` carry
coordinates to coordinates — which pins `m` down as
`Stacks.Sheaves.inverseImageForkComparison`.  Then `m` is an isomorphism as soon as, at every
geometric point of `X`, the coordinatewise map along the stalk of the structure map `α` is a
bijection from the solutions of `P` over the stalk of `g⁻¹𝒪` onto the solutions of `P` over the
stalk of `𝒪'`.

This is the source's reduction and nothing more: the geometric points of `X` are a conservative
family of points of its small étale site by Stacks 021B
(`AlgebraicGeometry.isIso_iff_forall_bijective_sheafFiber`), and at each of them
`Stacks.Sheaves.bijective_map_of_comp_forkι` identifies the two stalks with the two solution
sets.  The hypothesis is what Stacks 04GX supplies in the source, through
`AlgebraicGeometry.etaleStalkRingEquiv` and the locality of
`AlgebraicGeometry.isLocalHom_sheafFiber_fSharpInverseImage`. -/
theorem isIso_of_forall_bijOn_objSolutions
    (hι : ι ≫ CommRingObj.evalSystemHom
        (Stacks.underlyingRingSheaf (SmallEtale.topology B Y hY) O) c κ P =
      ι ≫ CommRingObj.zeroSystemHom
        (Stacks.underlyingRingSheaf (SmallEtale.topology B Y hY) O) κ ν)
    (hs : IsLimit (Fork.ofι ι hι))
    {T : Sheaf (SmallEtale.topology B X hX) (Type u)}
    {ι' : T ⟶ ∏ᶜ fun _ : κ =>
      Stacks.underlyingRingSheaf (SmallEtale.topology B X hX) O'}
    (h' : ι' ≫ CommRingObj.evalSystemHom
        (Stacks.underlyingRingSheaf (SmallEtale.topology B X hX) O') c' κ P =
      ι' ≫ CommRingObj.zeroSystemHom
        (Stacks.underlyingRingSheaf (SmallEtale.topology B X hX) O') κ ν)
    (hl' : IsLimit (Fork.ofι ι' h'))
    (m : f.inverseImage.obj H ⟶ T)
    (hm : m ≫ ι' = inverseImageCoordinates f O α κ ι)
    (hbij : ∀ s : GeometricPoint X,
      Set.BijOn
        (fun a : κ → ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)).obj
            (Stacks.underlyingRingSheaf (SmallEtale.topology B X hX)
              (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
      (SmallEtale.topology B X hX) f.inverseImage O)) =>
          fun i => ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)).map
            (PolynomialSystem.underlyingMap α) (a i))
        (PolynomialSystem.objSolutions
          ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)) κ P
          (pullbackCommRingSheaf (K := SmallEtale.topology B Y hY)
      (SmallEtale.topology B X hX) f.inverseImage O) c₁)
        (PolynomialSystem.objSolutions
          ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)) κ P O' c')) :
    IsIso m :=
  (isIso_iff_forall_bijective_sheafFiber B X hX m).2 fun s =>
    bijective_map_of_comp_forkι f O κ ι c c₁ hc₁ α c' P hι hs h' hl' m hm
      ((geometricPointSitePoint B X hX s).sheafFiber (A := Type u)) (hbij s)

end Stacks.EtaleCohomology

end
