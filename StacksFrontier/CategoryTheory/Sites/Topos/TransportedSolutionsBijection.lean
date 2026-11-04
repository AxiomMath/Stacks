module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.StalkReflectsUnits
public import StacksFrontier.CategoryTheory.Sites.Topos.PolynomialSystemTransported
public import StacksFrontier.RingTheory.Henselian.EtaleSolutionsCoefficients

/-!
# The solutions of a polynomial system over a transported ring, along a morphism of sheaves

Let `(C, J)` be a site, `α : 𝒪 ⟶ 𝒪'` a morphism of sheaves of commutative rings on it, and `Q` a
left exact functor to sets.  `StacksFrontier.CategoryTheory.Sites.Topos.PolynomialSystemTransported`
equips `Q(𝒪)` and `Q(𝒪')` with the transported ring structures and describes, as
`Stacks.Sheaves.PolynomialSystem.objSolutions`, the solutions over them of a polynomial system
whose coefficients are named by a ring homomorphism from an abstract coefficient ring `Γ`.  This
file transports `Q(α)` to a ring homomorphism between those two rings and proves that it is a
bijection of solution sets as soon as the two transported rings are strictly henselian local
rings, the system is étale over `Γ`, and `Q` reflects units for `α`.

This is step (4) of the proof of
[Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6), at the point where it
becomes ring theory.  Three of its inputs are supplied here and nothing geometric enters.

* `Q(α)` *is* a ring homomorphism: `CategoryTheory.Sheaf.ringObjMap` already says so for sheaves
  of rings, and `Stacks.Sheaves.PolynomialSystem.objMapRingHom` is that statement at the
  commutative structure, with `Q.map (underlyingMap α)` as its underlying function by `rfl`.
* It is a *local* homomorphism as soon as `Q` reflects units for `α` in the sense of
  `AlgebraicGeometry.RingedTopos.ReflectsUnitsObj`, which is condition (3) of Stacks 04H9:
  `AlgebraicGeometry.RingedTopos.isUnit_iff_exists_map_unitsIncl` says that a point of a
  transported ring is invertible exactly when it lifts through the transported units subsheaf,
  which is the hypothesis and the conclusion of reflection of units read as invertibility.  No
  stalk and no comparison with a fibre taken in commutative rings is involved, so this holds for
  every left exact `Q`.
* The system stays étale after its coefficients are read into the transported ring, which is
  `etale_baseChange_presentation` inside `bijOn_eval₂_solutions_of_etale`.

What is *not* here is the strict henselianity of the two transported rings: it is a hypothesis,
to be discharged at a geometric point of the small étale site of a scheme, where the transported
stalk ring is the étale local ring of Stacks 03PS.

## Main definitions

* `Stacks.Sheaves.PolynomialSystem.objMapRingHom`: a morphism of sheaves of commutative rings,
  read along `Q`, as a homomorphism of the transported rings.

## Main results

* `Stacks.Sheaves.PolynomialSystem.isLocalHom_objMapRingHom`: **reflection of units makes the
  transported map local**, condition (3) of Stacks 04H9 at an arbitrary left exact functor.
* `Stacks.Sheaves.PolynomialSystem.bijOn_objSolutions_of_etale`: **the transported map is a
  bijection of solution sets**, Stacks 04GX over the transported rings.

## References

* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CommRingObj Obj

universe t w v u

namespace Stacks.Sheaves.PolynomialSystem

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget CommRingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})]

attribute [local instance] Stacks.sheafCommRingObj

/-! ### A morphism of sheaves of commutative rings, read along the functor -/

section Map

variable {O O' : Sheaf J CommRingCat.{w}} (Q : Sheaf J (Type w) ⥤ Type t)
  [PreservesFiniteProducts Q]

/-- **A morphism of sheaves of commutative rings, read along a finite-product-preserving functor
to sets, is a homomorphism of the transported rings.**

It is `CategoryTheory.Sheaf.ringObjMap` of the underlying morphism of sheaves of rings: the
transported commutative ring structure of
`Stacks.Sheaves.PolynomialSystem.objCommRing` has that of
`CategoryTheory.Sheaf.ringObjRing` as its ring structure, so no new verification is needed. -/
def objMapRingHom (α : O ⟶ O') :
    letI := objCommRing O Q
    letI := objCommRing O' Q
    Q.obj (Stacks.underlyingRingSheaf J O) →+* Q.obj (Stacks.underlyingRingSheaf J O') :=
  CategoryTheory.Sheaf.ringObjMap ((Stacks.forgetCommRingSheaf J).map α) Q

/-- The underlying function of `Stacks.Sheaves.PolynomialSystem.objMapRingHom` is the value of
the functor on the underlying morphism of sheaves of sets. -/
theorem objMapRingHom_apply (α : O ⟶ O') (x : Q.obj (Stacks.underlyingRingSheaf J O)) :
    objMapRingHom Q α x = Q.map (underlyingMap α) x :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **A global section pushed along `α` is its reading in `Q(𝒪)` pushed along `Q(α)`.**  Both
sides are the value of `Q` on a composite at the point of the image of the terminal sheaf, so
this is `CategoryTheory.Functor.map_comp_apply` and nothing else.  It is what turns a
compatibility of the two coefficient maps over the site into the compatibility of their readings
at a point that `Stacks.Sheaves.PolynomialSystem.bijOn_objSolutions_of_etale` asks for. -/
theorem map_objGlobalRingHom (α : O ⟶ O')
    (g : 𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O) :
    Q.map (underlyingMap α) (objGlobalRingHom O Q g) =
      objGlobalRingHom O' Q (g ≫ underlyingMap α) :=
  (Q.map_comp_apply g (underlyingMap α) _).symm

end Map

/-! ### Locality of the transported map -/

section Local

variable [LocallySmall.{w} C] {O O' : Sheaf J CommRingCat.{w}}
  (Q : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteLimits Q]

omit [LocallySmall.{w} C] in
open AlgebraicGeometry.RingedTopos in
/-- **A left exact functor reflecting units for `α` makes the transported map a local
homomorphism.**

This is condition (3) of [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
read at the transported rings themselves rather than at a fibre taken in commutative rings.  By
`AlgebraicGeometry.RingedTopos.isUnit_iff_exists_map_unitsIncl` a point of a transported ring is
invertible exactly when it lifts through the image of the units subsheaf, and that is literally
what `AlgebraicGeometry.RingedTopos.ReflectsUnitsObj` transfers backwards along `α`. -/
theorem isLocalHom_objMapRingHom (α : O ⟶ O') (h : ReflectsUnitsObj Q α) :
    letI := objCommRing O Q
    letI := objCommRing O' Q
    IsLocalHom (objMapRingHom Q α) := by
  let := objCommRing O Q
  let := objCommRing O' Q
  refine ⟨fun a ha => ?_⟩
  refine (isUnit_iff_exists_map_unitsIncl (ofStructureSheaf J O) Q a).2 (h a ?_)
  exact (isUnit_iff_exists_map_unitsIncl (ofStructureSheaf J O') Q _).1 ha

end Local

/-! ### The bijection of solution sets -/

section Bijection

variable [LocallySmall.{w} C] (O O' : Sheaf J CommRingCat.{w})
  (Q : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteLimits Q]

-- The hypotheses that the transported rings are strictly henselian local rings have to be
-- stated at a ring structure on them, and `Stacks.Sheaves.PolynomialSystem.objCommRing` is
-- deliberately not an instance (see its own documentation).  It is made one for this section,
-- and for the statement below only: unlike `CategoryTheory.Sheaf.ringObjRing` its type is
-- already at the `Stacks.underlyingRingSheaf` spelling, so instance search finds it there, and
-- a consumer that makes it a local instance too sees exactly the hypotheses stated here.
attribute [local instance] objCommRing

omit [LocallySmall.{w} C] in
open AlgebraicGeometry.RingedTopos in
/-- **Stacks 04GX over the transported rings: the transported map is a bijection of solution
sets.**

Let `P₁, …, P_n ∈ Γ[x₁, …, x_n]` be a system presenting an étale `Γ`-algebra, let `α : 𝒪 ⟶ 𝒪'`
be a morphism of sheaves of commutative rings whose coefficient maps `c` and `c'` agree along
`α`, and let `Q` be a left exact functor to sets for which the two transported rings `Q(𝒪)` and
`Q(𝒪')` are strictly henselian local rings and which reflects units for `α`.  Then the
coordinatewise map along `Q(α)` is a bijection from the solutions of the system over `Q(𝒪)` onto
its solutions over `Q(𝒪')`.

This is [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX) in the form
`bijOn_eval₂_solutions_of_etale`, fed with
`Stacks.Sheaves.PolynomialSystem.isLocalHom_objMapRingHom` for the locality of the map and with
the hypothesis `hc` for the compatibility of the two readings of the coefficients.  It is the
hypothesis of `Stacks.EtaleCohomology.isIso_of_forall_bijOn_objSolutions`, at one geometric
point, with the strict henselianity of the two stalks left to be supplied. -/
theorem bijOn_objSolutions_of_etale (α : O ⟶ O')
    {Γ : Type*} [CommRing Γ] {n : ℕ} (P : Fin n → MvPolynomial (Fin n) Γ)
    [Algebra.Etale Γ (MvPolynomial (Fin n) Γ ⧸ Ideal.span (Set.range P))]
    (c : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O))
    (c' : Γ →+* (𝟙_ (Sheaf J (Type w)) ⟶ Stacks.underlyingRingSheaf J O'))
    [HenselianLocalRing (Q.obj (Stacks.underlyingRingSheaf J O))]
    [HenselianLocalRing (Q.obj (Stacks.underlyingRingSheaf J O'))]
    [IsSepClosed (IsLocalRing.ResidueField (Q.obj (Stacks.underlyingRingSheaf J O)))]
    [IsSepClosed (IsLocalRing.ResidueField (Q.obj (Stacks.underlyingRingSheaf J O')))]
    (hu : ReflectsUnitsObj Q α)
    (hc : ∀ r, Q.map (underlyingMap α) (objGlobalRingHom O Q (c r)) =
      objGlobalRingHom O' Q (c' r)) :
    Set.BijOn (fun a : Fin n → Q.obj (Stacks.underlyingRingSheaf J O) =>
        fun i => Q.map (underlyingMap α) (a i))
      (objSolutions Q (Fin n) P O c) (objSolutions Q (Fin n) P O' c') :=
  bijOn_eval₂_solutions_of_etale ((objGlobalRingHom O Q).comp c) (objMapRingHom Q α)
    (isLocalHom_objMapRingHom Q α hu) ((objGlobalRingHom O' Q).comp c')
    (RingHom.ext fun r => (hc r).symm) P

end Bijection

end Stacks.Sheaves.PolynomialSystem

end
