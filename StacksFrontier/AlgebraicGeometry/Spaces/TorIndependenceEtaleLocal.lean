module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependence
import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing

/-!
# Tor independence of algebraic spaces is étale local

Tor independence of two algebraic spaces over a base, Stacks 08IP, is a condition on the
étale local rings at compatible triples of geometric points.  An étale morphism does not
change the étale local ring, so the condition is insensitive to replacing either of the two
spaces, or the base, by an étale cover: that is the equivalence of conditions (1) and (2) of
Stacks 08IQ, which is what this file proves first.  Combined with the lifting of geometric
points along an étale surjective morphism, Stacks 05VN, it also gives condition (3) of
Stacks 08IQ — one étale surjective diagram of charts suffices — which is the form in which
Tor independence of algebraic spaces is checked on charts.

All four conditions of Stacks 08IQ are equivalent.  Conditions (1), (2) and (3) are related
here; condition (4), which is condition (3) for a diagram whose three upper terms are *schemes*
with Tor independence read on their ordinary local rings in the sense of Stacks 08IA, is
compared with condition (1) in the two companion files
`StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeComparison`, which proves
(4) ⟹ (1), and `StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeConverse`, which
proves (1) ⟹ (4).

The input is `AlgebraicGeometry.Space.etaleLocalRingIsoOfIsEtale`, the canonical isomorphism
of étale local rings along an étale morphism.  Everything here is deduced from the one fact
that the isomorphism is *germwise* canonical: on the germ of a section over a small étale
neighbourhood `N` of the source point it is the germ of the same section over the image of `N`
under postcomposition.  This is
`AlgebraicGeometry.Space.etaleLocalRingGerm_comp_etaleLocalRingIsoOfIsEtale`, and it is the
reason that the existential of `AlgebraicGeometry.Space.TorIndependent` — which asks only for
*some* homomorphism of étale local rings satisfying
`AlgebraicGeometry.Space.IsEtaleLocalRingMap`, because no canonical homomorphism is available
for a general morphism of algebraic spaces — can be discharged with the canonical isomorphism
whenever the morphism happens to be étale.

## Main results

* `AlgebraicGeometry.Space.etaleLocalRingGerm_comp_etaleLocalRingIsoOfIsEtale` and
  `AlgebraicGeometry.Space.etaleLocalRingIsoOfIsEtale_inv_comp_etaleLocalRingGerm`: the
  canonical isomorphism along an étale morphism carries germs to germs.
* `AlgebraicGeometry.Space.isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv`: the inverse of
  the canonical isomorphism is a germ-compatible homomorphism of étale local rings in the sense
  of `AlgebraicGeometry.Space.IsEtaleLocalRingMap`.  This is the first consumer of that
  predicate.
* `AlgebraicGeometry.Space.torIndependent_comp_of_isEtale_source`: Tor independence over a base
  is inherited by étale covers of the two spaces.
* `AlgebraicGeometry.Space.torIndependent_of_comp_isEtale_base`: Tor independence over a base
  descends to Tor independence over an étale cover of the base.
* `AlgebraicGeometry.Space.torIndependent_iff_forall_etale_diagram` is Stacks 08IQ, the
  equivalence of its conditions (1) and (2).
* `AlgebraicGeometry.Space.torIndependent_of_isEtale_surjective_diagram` is Stacks 08IQ,
  condition (3) implies condition (1): Tor independence over the base follows from Tor
  independence in one diagram of étale charts which is surjective over the base changes.
* `AlgebraicGeometry.Space.exists_isEtale_surjective_diagram_of_torIndependent` is Stacks 08IQ,
  condition (1) implies condition (3): the diagram of identities witnesses the existence.

Condition (4) is carried by the two companion files:
`AlgebraicGeometry.Space.torIndependent_of_torIndependent_scheme_diagram` is (4) ⟹ (1) and
`AlgebraicGeometry.Space.exists_torIndependent_scheme_diagram_of_torIndependent` is (1) ⟹ (4),
so the four conditions of Stacks 08IQ are equivalent.

## Implementation notes

The germ statement is proved at the level of the colimit cocone,
`AlgebraicGeometry.Space.colimit_ι_comp_etaleLocalRingIsoOfIsEtale`: the canonical isomorphism
is a composite of `CategoryTheory.Limits.HasColimit.isoOfNatIso` along an equality of diagrams
that holds on the nose with the comparison of
`CategoryTheory.Functor.Final.colimitIso`, so the cocone component at `N` is carried to the
cocone component at the postcomposition of `N` with no transport beyond an `eqToHom` of a
reflexivity proof.

Conditions (1) and (2) of Stacks 08IQ are related through two separate statements, one changing
the two spaces and one changing the base, which are composed by rewriting the structure
morphism of the base along the commutativity of the two squares of the diagram of (2).  That is
what keeps every geometric point appearing in the proof *syntactically* the image of the point
being considered: `AlgebraicGeometry.Space.geometricPointMap` is functorial by `rfl`, so
`geometricPointMap (a ≫ f) x` and `geometricPointMap f (geometricPointMap a x)` are the same
term, and no transport along an equality of geometric points is needed in either half.  Only
the compatibility of the two étale comparisons at the two points of the base, which is
`AlgebraicGeometry.Space.etaleLocalRingIsoOfIsEtale_congr`, carries an `eqToHom`.

Tor independence is transported along ring isomorphisms by the private
`torIndependent_of_ringEquiv`, stated with the two algebra structures given as explicit ring
homomorphisms rather than as instances, so that it applies to the `RingHom.toAlgebra` structures
that `AlgebraicGeometry.Space.TorIndependent` builds from its existential witnesses.

For condition (3) the existential witnesses cannot be produced by conjugating the given ones
with the étale comparisons, because the germ condition for the conjugate is not available
directly.  They are instead the canonical homomorphisms of Stacks 04NG, and the compatibility
square needed for the transport comes from their uniqueness: both ways around the square are
homomorphisms induced by the one composite morphism `U ⟶ W ⟶ B = U ⟶ X ⟶ B`, so they agree.
The geometric points of the two charts are produced by lifting a compatible pair of geometric
points through the cartesian squares defining the two base changes — which is possible over the
same field, the sections of a fibre product of presheaves being compatible pairs of sections —
and then along the étale surjective chart morphisms by Stacks 05VN.

## References

* [Stacks Project, Tag 08IQ](https://stacks.math.columbia.edu/tag/08IQ)
* [Stacks Project, Tag 08IP](https://stacks.math.columbia.edu/tag/08IP)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The canonical comparison of étale local rings is germwise canonical -/

/-- The canonical isomorphism of étale local rings along an étale morphism carries the
colimit cocone component at a small étale neighbourhood `N` of the source point to the cocone
component at the image of `N` under postcomposition. -/
public theorem colimit_ι_comp_etaleLocalRingIsoOfIsEtale {Y X : AlgebraicSpaces B S hS}
    (φ : Y ⟶ X) (hφ : IsEtale B S hS φ.hom) (y : GeometricPoint B S hS Y.1)
    (N : SmallEtaleNeighborhood y) :
    colimit.ι (SmallEtaleNeighborhood.sections (x := y)
        (liftedStructurePresheaf B S hS Y.1)) (Opposite.op N) ≫
        (etaleLocalRingIsoOfIsEtale B S hS φ hφ y).hom =
      colimit.ι (SmallEtaleNeighborhood.sections
        (x := geometricPointMap φ.hom y) (liftedStructurePresheaf B S hS X.1))
        (Opposite.op ((SmallEtaleNeighborhood.postcomp B S hS φ hφ y).obj N)) := by
  have := SmallEtaleNeighborhood.initial_postcomp B S hS φ hφ y
  rw [etaleLocalRingIsoOfIsEtale]
  simp only [Iso.trans_hom, HasColimit.ι_isoOfNatIso_hom_assoc,
    Functor.Final.ι_colimitIso_hom, eqToIso.hom, eqToHom_app]
  rfl

/-- The canonical isomorphism of étale local rings along an étale morphism takes the germ of a
section over a small étale neighbourhood of the source point to the germ of the same section
over the image of that neighbourhood under postcomposition. -/
public theorem etaleLocalRingGerm_comp_etaleLocalRingIsoOfIsEtale
    {Y X : AlgebraicSpaces B S hS} (φ : Y ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (y : GeometricPoint B S hS Y.1) (N : SmallEtaleNeighborhood y) :
    ((etaleLocalRingIsoOfIsEtale B S hS φ hφ y).hom.hom).comp
        (etaleLocalRingGerm B S hS Y.1 y (Opposite.op N)) =
      etaleLocalRingGerm B S hS X.1 (geometricPointMap φ.hom y)
        (Opposite.op ((SmallEtaleNeighborhood.postcomp B S hS φ hφ y).obj N)) :=
  RingHom.ext fun a =>
    DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom
        (colimit_ι_comp_etaleLocalRingIsoOfIsEtale B S hS φ hφ y N))
      (ULift.up a)

/-- The inverse of the canonical isomorphism of étale local rings along an étale morphism takes
the germ of a section over the postcomposition of a small étale neighbourhood back to the germ
of the same section over that neighbourhood. -/
public theorem etaleLocalRingIsoOfIsEtale_inv_comp_etaleLocalRingGerm
    {Y X : AlgebraicSpaces B S hS} (φ : Y ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (y : GeometricPoint B S hS Y.1) (N : SmallEtaleNeighborhood y) :
    ((etaleLocalRingIsoOfIsEtale B S hS φ hφ y).inv.hom).comp
        (etaleLocalRingGerm B S hS X.1 (geometricPointMap φ.hom y)
          (Opposite.op ((SmallEtaleNeighborhood.postcomp B S hS φ hφ y).obj N))) =
      etaleLocalRingGerm B S hS Y.1 y (Opposite.op N) :=
  RingHom.ext fun a =>
    DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom
        ((Iso.comp_inv_eq _).mpr
          (colimit_ι_comp_etaleLocalRingIsoOfIsEtale B S hS φ hφ y N).symm))
      (ULift.up a)

/-- Germs over a refinement of small étale neighbourhoods agree: the germ at the refinement of
the restriction of a section is the germ of the section. -/
public theorem etaleLocalRingGerm_comp_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : GeometricPoint B S hS F} {N M : SmallEtaleNeighborhood z} (h : N ⟶ M) :
    (etaleLocalRingGerm B S hS F z (Opposite.op N)).comp
        (CommRingCat.Hom.hom (Scheme.Γ.map
          ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map h.hom)).op)) =
      etaleLocalRingGerm B S hS F z (Opposite.op M) :=
  RingHom.ext fun a =>
    DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom
        (colimit.w (SmallEtaleNeighborhood.sections (x := z)
          (liftedStructurePresheaf B S hS F)) h.op))
      (ULift.up a)

/-- **The canonical map witnesses the existential of Stacks 08IP for an étale morphism.**  For
an étale morphism of algebraic spaces the inverse of
`AlgebraicGeometry.Space.etaleLocalRingIsoOfIsEtale` is a germ-compatible homomorphism of étale
local rings in the sense of `AlgebraicGeometry.Space.IsEtaleLocalRingMap`.

So in the étale case the homomorphism that the definition of Tor independence of algebraic
spaces asks for merely existing is available canonically. -/
public theorem isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv
    {Y X : AlgebraicSpaces B S hS} (φ : Y ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (y : GeometricPoint B S hS Y.1) :
    IsEtaleLocalRingMap φ.hom y (etaleLocalRingIsoOfIsEtale B S hS φ hφ y).inv.hom := by
  intro N M g hover hpoint
  rw [← etaleLocalRingIsoOfIsEtale_inv_comp_etaleLocalRingGerm B S hS φ hφ y N,
    ← etaleLocalRingGerm_comp_map B S hS (F := X.1) (z := geometricPointMap φ.hom y)
      (N := (SmallEtaleNeighborhood.postcomp B S hS φ hφ y).obj N) (M := M)
      { hom := ObjectProperty.homMk (CostructuredArrow.homMk g hover.symm)
        point_comp := hpoint }]
  rfl

/-- The canonical comparison of étale local rings along an étale morphism is compatible with an
equality of geometric points of the source. -/
public theorem etaleLocalRingIsoOfIsEtale_congr {Y X : AlgebraicSpaces B S hS} (φ : Y ⟶ X)
    (hφ : IsEtale B S hS φ.hom) {y y' : GeometricPoint B S hS Y.1} (hy : y = y') :
    eqToHom (congrArg (etaleLocalRing B S hS Y.1) hy) ≫
        (etaleLocalRingIsoOfIsEtale B S hS φ hφ y').hom =
      (etaleLocalRingIsoOfIsEtale B S hS φ hφ y).hom ≫
        eqToHom (congrArg (etaleLocalRing B S hS X.1)
          (congrArg (geometricPointMap φ.hom) hy)) := by
  cases hy
  simp

/-! ### Transport of Tor independence along ring isomorphisms -/

/-- Tor independence of two algebras is transported along isomorphisms of the base ring and of
the two algebras which are compatible with the two structure homomorphisms.  The structure
homomorphisms are explicit, rather than instance arguments, so that the statement applies to
the `RingHom.toAlgebra` structures of `AlgebraicGeometry.Space.TorIndependent`. -/
private theorem torIndependent_of_ringEquiv
    {R A C R' A' C' : Type v} [CommRing R] [CommRing A] [CommRing C]
    [CommRing R'] [CommRing A'] [CommRing C']
    (f : R →+* A) (g : R →+* C) (f' : R' →+* A') (g' : R' →+* C')
    (eR : R ≃+* R') (eA : A ≃+* A') (eC : C ≃+* C')
    (hA : ∀ r, eA (f r) = f' (eR r))
    (hC : ∀ r, eC (g r) = g' (eR r))
    (h : @RingTheory.TorIndependence.TorIndependent R A C _ _ _
      f.toAlgebra g.toAlgebra) :
    @RingTheory.TorIndependence.TorIndependent R' A' C' _ _ _
      f'.toAlgebra g'.toAlgebra := by
  let : Algebra R A := f.toAlgebra
  let : Algebra R C := g.toAlgebra
  let : Algebra R' A' := f'.toAlgebra
  let : Algebra R' C' := g'.toAlgebra
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor] at h
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
  let Fres := ModuleCat.restrictScalars eR.toRingHom
  have mkIso : ∀ {M M' : Type v} [CommRing M] [CommRing M'] [Algebra R M] [Algebra R' M']
      (e : M ≃+* M') (he : ∀ r, e (algebraMap R M r) = algebraMap R' M' (eR r)),
      ModuleCat.of R M ≅ Fres.obj (ModuleCat.of R' M') := fun {M M'} _ _ _ _ e he =>
    LinearEquiv.toModuleIso (show M ≃ₗ[R] (Fres.obj (ModuleCat.of R' M')) from
      { toFun := e
        invFun := e.symm
        left_inv := e.left_inv
        right_inv := e.right_inv
        map_add' := e.map_add
        map_smul' := fun r a ↦ by
          change e (r • a) = (eR r) • e a
          rw [Algebra.smul_def, Algebra.smul_def, e.map_mul]
          exact congrArg (· * e a) (he r) })
  intro i hi
  apply (RingTheory.TorIndependence.isZero_tor_restrict_iff eR
    (ModuleCat.of R' A') (ModuleCat.of R' C') i).mp
  rw [← (((CategoryTheory.Tor (ModuleCat R) i).mapIso (mkIso eA hA)).app
    (Fres.obj (ModuleCat.of R' C'))).isZero_iff,
    ← (((CategoryTheory.Tor (ModuleCat R) i).obj (ModuleCat.of R A)).mapIso
      (mkIso eC hC)).isZero_iff]
  exact h i hi

/-! ### Tor independence is étale local on the two spaces and on the base -/

/-- A germ-compatible homomorphism of étale local rings over `f` at the image of a point under an
étale morphism `φ` gives one over `φ ≫ f`, after precomposing with the inverse of the canonical
isomorphism. -/
private theorem isEtaleLocalRingMap_comp_iso_inv {Y X : AlgebraicSpaces B S hS}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : Y ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (y : GeometricPoint B S hS Y.1) (f : X.1 ⟶ Z)
    (ψ : etaleLocalRing B S hS Z (geometricPointMap f (geometricPointMap φ.hom y)) →+*
      etaleLocalRing B S hS X.1 (geometricPointMap φ.hom y))
    (h : IsEtaleLocalRingMap f (geometricPointMap φ.hom y) ψ) :
    IsEtaleLocalRingMap (φ.hom ≫ f) y
      (((etaleLocalRingIsoOfIsEtale B S hS φ hφ y).inv.hom).comp ψ) := by
  intro N M g hover hpoint
  have key := h ((SmallEtaleNeighborhood.postcomp B S hS φ hφ y).obj N) M g
    ((Category.assoc _ _ _).trans hover) hpoint
  rw [← etaleLocalRingIsoOfIsEtale_inv_comp_etaleLocalRingGerm B S hS φ hφ y N]
  exact congrArg
    (RingHom.comp (CommRingCat.Hom.hom (etaleLocalRingIsoOfIsEtale B S hS φ hφ y).inv)) key

/-- A germ-compatible homomorphism of étale local rings over `u ≫ c` gives one over `u` after
precomposing with the canonical isomorphism along the étale morphism `c`. -/
private theorem isEtaleLocalRingMap_comp_iso_hom {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W Bs : AlgebraicSpaces B S hS} (c : W ⟶ Bs) (hc : IsEtale B S hS c.hom) (u : U ⟶ W.1)
    (ubar : GeometricPoint B S hS U)
    (φ : etaleLocalRing B S hS Bs.1 (geometricPointMap c.hom (geometricPointMap u ubar)) →+*
      etaleLocalRing B S hS U ubar)
    (h : IsEtaleLocalRingMap (u ≫ c.hom) ubar φ) :
    IsEtaleLocalRingMap u ubar
      (φ.comp (etaleLocalRingIsoOfIsEtale B S hS c hc (geometricPointMap u ubar)).hom.hom) := by
  intro N M g hover hpoint
  have key := h N ((SmallEtaleNeighborhood.postcomp B S hS c hc (geometricPointMap u ubar)).obj M)
    g ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ c.hom) hover).trans (Category.assoc _ _ _))) hpoint
  exact key.trans (congrArg (RingHom.comp φ)
    (etaleLocalRingGerm_comp_etaleLocalRingIsoOfIsEtale B S hS c hc _ M)).symm

/-- Tor independence of two algebraic spaces over a base passes to étale covers of the two
spaces: if `X` and `Y` are Tor independent over `B` and `U ⟶ X`, `V ⟶ Y` are étale, then `U`
and `V` are Tor independent over `B`. -/
public theorem torIndependent_comp_of_isEtale_source {Bs X Y U V : AlgebraicSpaces B S hS}
    (fX : X.1 ⟶ Bs.1) (gY : Y.1 ⟶ Bs.1)
    {a : U ⟶ X} (ha : IsEtale B S hS a.hom) {b : V ⟶ Y} (hb : IsEtale B S hS b.hom)
    (h : TorIndependent X.2 Y.2 Bs.2 fX gY) :
    TorIndependent U.2 V.2 Bs.2 (a.hom ≫ fX) (b.hom ≫ gY) := by
  intro ubar vbar hpt
  obtain ⟨φ, ψ, hφ, hψ, htor⟩ := h (geometricPointMap a.hom ubar)
    (geometricPointMap b.hom vbar) hpt
  refine ⟨((etaleLocalRingIsoOfIsEtale B S hS a ha ubar).inv.hom).comp φ,
    ((etaleLocalRingIsoOfIsEtale B S hS b hb vbar).inv.hom).comp ψ,
    isEtaleLocalRingMap_comp_iso_inv B S hS a ha ubar fX φ hφ,
    isEtaleLocalRingMap_comp_iso_inv B S hS b hb vbar gY ψ hψ, ?_⟩
  exact torIndependent_of_ringEquiv _ _ _ _ (RingEquiv.refl _)
      (etaleLocalRingIsoOfIsEtale B S hS a ha ubar).symm.commRingCatIsoToRingEquiv
      (etaleLocalRingIsoOfIsEtale B S hS b hb vbar).symm.commRingCatIsoToRingEquiv
      (fun _ => rfl) (fun _ => rfl) htor

/-- Tor independence of two algebraic spaces over a base descends to an étale cover of the
base: if `U` and `V` are Tor independent over `B` through morphisms factoring over an étale
`W ⟶ B`, then they are Tor independent over `W`. -/
public theorem torIndependent_of_comp_isEtale_base {Bs W U V : AlgebraicSpaces B S hS}
    {c : W ⟶ Bs} (hc : IsEtale B S hS c.hom) (uw : U ⟶ W) (vw : V ⟶ W)
    (h : TorIndependent U.2 V.2 Bs.2 (uw.hom ≫ c.hom) (vw.hom ≫ c.hom)) :
    TorIndependent U.2 V.2 W.2 uw.hom vw.hom := by
  intro ubar vbar hpt
  obtain ⟨φ, ψ, hφ, hψ, htor⟩ := h ubar vbar (congrArg (geometricPointMap c.hom) hpt)
  refine ⟨φ.comp
      (etaleLocalRingIsoOfIsEtale B S hS c hc (geometricPointMap uw.hom ubar)).hom.hom,
    ψ.comp
      (etaleLocalRingIsoOfIsEtale B S hS c hc (geometricPointMap vw.hom vbar)).hom.hom,
    isEtaleLocalRingMap_comp_iso_hom B S hS c hc uw.hom ubar φ hφ,
    isEtaleLocalRingMap_comp_iso_hom B S hS c hc vw.hom vbar ψ hψ, ?_⟩
  have hmor : (etaleLocalRingIsoOfIsEtale B S hS c hc
        (geometricPointMap uw.hom ubar)).inv ≫
      eqToHom (congrArg (etaleLocalRing B S hS W.1) hpt) ≫
        (etaleLocalRingIsoOfIsEtale B S hS c hc
          (geometricPointMap vw.hom vbar)).hom =
    eqToHom (congrArg (etaleLocalRing B S hS Bs.1)
      (congrArg (geometricPointMap c.hom) hpt)) := by
    rw [etaleLocalRingIsoOfIsEtale_congr B S hS c hc hpt, Iso.inv_hom_id_assoc]
  refine torIndependent_of_ringEquiv _ _ _ _
    (etaleLocalRingIsoOfIsEtale B S hS c hc
      (geometricPointMap uw.hom ubar)).symm.commRingCatIsoToRingEquiv
    (RingEquiv.refl _) (RingEquiv.refl _) (fun r => ?_) (fun r => ?_) htor
  · exact congrArg φ (DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom
        ((etaleLocalRingIsoOfIsEtale B S hS c hc
          (geometricPointMap uw.hom ubar)).inv_hom_id)) r).symm
  · exact congrArg ψ
      (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmor) r).symm

/-! ### Stacks 08IQ, the equivalence of conditions (1) and (2) -/

/-- **Stacks 08IQ, (1) ⟺ (2).**  Let `X` and `Y` be algebraic spaces over an algebraic space
`B`.  Then `X` and `Y` are Tor independent over `B` if and only if for every commutative
diagram
```
U ⟶ W ⟵ V
↓    ↓    ↓
X ⟶ B ⟵ Y
```
with étale vertical arrows, `U` and `V` are Tor independent over `W`.

Condition (3), which asks for a single such diagram in which `W ⟶ B` is surjective and the
two upper terms are étale surjective over the base changes `X ×_B W` and `Y ×_B W`, is
equivalent to condition (1): it implies it by
`AlgebraicGeometry.Space.torIndependent_of_isEtale_surjective_diagram` and follows from it by
`AlgebraicGeometry.Space.exists_isEtale_surjective_diagram_of_torIndependent`.  Condition (4),
which reads the conclusion for `U`, `V` and `W` schemes in the sense of Stacks 08IA, that is on
ordinary local rings, implies condition (1) by
`AlgebraicGeometry.Space.torIndependent_of_torIndependent_scheme_diagram` in
`StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeComparison`, and follows from
condition (1) by
`AlgebraicGeometry.Space.exists_torIndependent_scheme_diagram_of_torIndependent` in
`StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeConverse`.  So the four conditions
of Stacks 08IQ are equivalent. -/
@[stacks 08IQ "(1) <=> (2)"]
public theorem torIndependent_iff_forall_etale_diagram {Bs X Y : AlgebraicSpaces B S hS}
    (fX : X ⟶ Bs) (gY : Y ⟶ Bs) :
    TorIndependent X.2 Y.2 Bs.2 fX.hom gY.hom ↔
      ∀ (U V W : AlgebraicSpaces B S hS) (a : U ⟶ X) (b : V ⟶ Y) (c : W ⟶ Bs)
        (uw : U ⟶ W) (vw : V ⟶ W), IsEtale B S hS a.hom → IsEtale B S hS b.hom →
        IsEtale B S hS c.hom → uw.hom ≫ c.hom = a.hom ≫ fX.hom →
        vw.hom ≫ c.hom = b.hom ≫ gY.hom → TorIndependent U.2 V.2 W.2 uw.hom vw.hom := by
  constructor
  · intro h U V W a b c uw vw ha hb hc hsq1 hsq2
    refine torIndependent_of_comp_isEtale_base B S hS hc uw vw ?_
    rw [hsq1, hsq2]
    exact torIndependent_comp_of_isEtale_source B S hS fX.hom gY.hom ha hb h
  · intro h
    exact h X Y Bs (𝟙 X) (𝟙 Y) (𝟙 Bs) fX gY
      (isEtale_of_isIso B S hS (𝟙 X.1)) (isEtale_of_isIso B S hS (𝟙 Y.1))
      (isEtale_of_isIso B S hS (𝟙 Bs.1)) (by simp) (by simp)

/-- Transport of an element of a commutative ring along an equality of objects of
`CommRingCat` and back is the identity. -/
private theorem eqToHom_hom_eqToHom_hom {R₁ R₂ : CommRingCat.{v}} (h : R₁ = R₂) (h' : R₂ = R₁)
    (s : R₁) : (eqToHom h').hom ((eqToHom h).hom s) = s := by
  subst h
  simp

/-- An isomorphism of commutative rings cancels its inverse on elements. -/
private theorem iso_hom_hom_inv_hom {R₁ R₂ : CommRingCat.{v}} (e : R₁ ≅ R₂) (t : R₂) :
    e.hom.hom (e.inv.hom t) = t := by
  simp

/-- Three successive transports of an element of a commutative ring along equalities of objects
of `CommRingCat` are the transport along their composite. -/
private theorem eqToHom_hom_trans₃ {R₁ R₂ R₃ R₄ : CommRingCat.{v}} (h₁ : R₁ = R₂) (h₂ : R₂ = R₃)
    (h₃ : R₃ = R₄) (h : R₁ = R₄) (s : R₁) :
    (eqToHom h₃).hom ((eqToHom h₂).hom ((eqToHom h₁).hom s)) = (eqToHom h).hom s := by
  subst h₁ h₂ h₃
  simp

/-- The inverse of an isomorphism of commutative rings cancels it on elements. -/
private theorem iso_inv_hom_hom_hom {R₁ R₂ : CommRingCat.{v}} (e : R₁ ≅ R₂) (t : R₁) :
    e.inv.hom (e.hom.hom t) = t := by
  simp

/-! ### Stacks 08IQ, condition (3) implies condition (1) -/

/-- A compatible pair of sections of the two middle terms of a cartesian square of presheaves
over one object of the site is the image of a section of its upper left corner. -/
private theorem exists_section_of_isPullback
    {Q Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : Q ⟶ Z} {q : Q ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f) (A : BigFppfOver B S hS)
    (vz : Z.obj (Opposite.op A)) (vx : X.obj (Opposite.op A))
    (hval : g.app (Opposite.op A) vz = f.app (Opposite.op A) vx) :
    ∃ vw : Q.obj (Opposite.op A),
      p.app (Opposite.op A) vw = vz ∧ q.app (Opposite.op A) vw = vx := by
  have hcompat : (yonedaEquiv.symm vz : yoneda.obj A ⟶ Z) ≫ g =
      (yonedaEquiv.symm vx : yoneda.obj A ⟶ X) ≫ f := by
    apply (yonedaEquiv (X := A) (F := Y)).injective
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hval
  refine ⟨yonedaEquiv (sq.lift _ _ hcompat), ?_, ?_⟩
  · have hl := congrArg (fun k : yoneda.obj A ⟶ Z => yonedaEquiv k)
      (sq.lift_fst (yonedaEquiv.symm vz) (yonedaEquiv.symm vx) hcompat)
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hl
  · have hl := congrArg (fun k : yoneda.obj A ⟶ X => yonedaEquiv k)
      (sq.lift_snd (yonedaEquiv.symm vz) (yonedaEquiv.symm vx) hcompat)
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hl

/-- A compatible pair of geometric points of the two middle terms of a cartesian square of
presheaves lifts to a geometric point of its upper left corner, over the same field. -/
private theorem exists_geometricPoint_of_isPullback
    {Q Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : Q ⟶ Z} {q : Q ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (z : GeometricPoint B S hS Z) (x : GeometricPoint B S hS X)
    (h : geometricPointMap g z = geometricPointMap f x) :
    ∃ w : GeometricPoint B S hS Q,
      geometricPointMap p w = z ∧ geometricPointMap q w = x := by
  obtain ⟨z, hz⟩ := z
  obtain ⟨x, hx⟩ := x
  have hv : FieldValuedPoint.map B S hS Z g z = FieldValuedPoint.map B S hS X f x :=
    congrArg Subtype.val h
  obtain ⟨kz, hcz, tz, vz⟩ := z
  rename_i instz
  obtain ⟨kx, hcx, tx, vx⟩ := x
  rename_i instx
  rw [FieldValuedPoint.mk.injEq] at hv
  obtain rfl : kz = kx := hv.1
  obtain rfl : instz = instx := eq_of_heq hv.2.1
  obtain rfl : hcz = hcx := rfl
  obtain rfl : tz = tx := eq_of_heq hv.2.2.1
  obtain ⟨vw, hw1, hw2⟩ := exists_section_of_isPullback B S hS sq
    (Over.mk (⟨tz⟩ : B.obj hcz ⟶ B.obj hS)) vz vx (eq_of_heq hv.2.2.2)
  refine ⟨⟨⟨kz, hcz, tz, vw⟩, hz⟩, Subtype.ext ?_, Subtype.ext ?_⟩
  · exact congrArg (fun v => (⟨kz, hcz, tz, v⟩ : FieldValuedPoint B S hS Z)) hw1
  · exact congrArg (fun v => (⟨kz, hcz, tz, v⟩ : FieldValuedPoint B S hS X)) hw2

/-- The germ characterisation of a homomorphism of étale local rings transported along an
equality of the inducing morphisms. -/
private theorem isEtaleLocalRingMap_of_morphism_eq
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m m' : F ⟶ H} (hm : m = m')
    (x : GeometricPoint B S hS F)
    (φ : etaleLocalRing B S hS H (geometricPointMap m x) →+* etaleLocalRing B S hS F x)
    (hφ : IsEtaleLocalRingMap m x φ) :
    IsEtaleLocalRingMap m' x (φ.comp (eqToHom (congrArg (etaleLocalRing B S hS H)
      (congrArg (fun k => geometricPointMap k x) hm).symm)).hom) := by
  subst hm
  simpa using hφ

/-- The two ways around a commutative square of morphisms of algebraic spaces induce the same
homomorphism of étale local rings at a geometric point of the upper left corner. -/
private theorem etaleLocalRingMap_comp_eq {U W X Bs : AlgebraicSpaces B S hS}
    (uw : U ⟶ W) (c : W ⟶ Bs) (a : U ⟶ X) (fX : X ⟶ Bs) (hsq : uw.hom ≫ c.hom = a.hom ≫ fX.hom)
    (ubar : GeometricPoint B S hS U.1)
    (h : geometricPointMap fX.hom (geometricPointMap a.hom ubar) =
      geometricPointMap c.hom (geometricPointMap uw.hom ubar)) :
    ((etaleLocalRingMap U.2 uw.hom ubar).comp
        (etaleLocalRingMap W.2 c.hom (geometricPointMap uw.hom ubar))).comp
        (eqToHom (congrArg (etaleLocalRing B S hS Bs.1) h)).hom =
      (etaleLocalRingMap U.2 a.hom ubar).comp
        (etaleLocalRingMap X.2 fX.hom (geometricPointMap a.hom ubar)) :=
  (existsUnique_etaleLocalRingMap U.2 (a.hom ≫ fX.hom) ubar).unique
    (isEtaleLocalRingMap_of_morphism_eq B S hS hsq ubar _
      (isEtaleLocalRingMap_comp U.2 W.2 uw.hom c.hom ubar
        (etaleLocalRingMap_isEtaleLocalRingMap U.2 uw.hom ubar)
        (etaleLocalRingMap_isEtaleLocalRingMap W.2 c.hom _)))
    (isEtaleLocalRingMap_comp U.2 X.2 a.hom fX.hom ubar
      (etaleLocalRingMap_isEtaleLocalRingMap U.2 a.hom ubar)
      (etaleLocalRingMap_isEtaleLocalRingMap X.2 fX.hom _))

/-- **Stacks 08IQ, (3) ⟹ (1).**  Let `X` and `Y` be algebraic spaces over an algebraic space
`Bs`.  Suppose given one commutative diagram
```
U ⟶ W ⟵ V
↓    ↓    ↓
X ⟶ Bs ⟵ Y
```
with étale vertical arrows in which `W ⟶ Bs` is surjective and in which `U` and `V` are étale
and surjective over the fibre products `X ×_{Bs} W` and `Y ×_{Bs} W`.  If `U` and `V` are Tor
independent over `W`, then `X` and `Y` are Tor independent over `Bs`.

The two fibre products are presented as arbitrary cartesian squares of the underlying
presheaves, which is how a fibre product of algebraic spaces is formed. -/
@[stacks 08IQ "(3) => (1)"]
public theorem torIndependent_of_isEtale_surjective_diagram
    {Bs X Y U V W PX PY : AlgebraicSpaces B S hS}
    (fX : X ⟶ Bs) (gY : Y ⟶ Bs) (c : W ⟶ Bs)
    (a : U ⟶ X) (uw : U ⟶ W) (b : V ⟶ Y) (vw : V ⟶ W)
    (pX : PX ⟶ X) (pW : PX ⟶ W) (qY : PY ⟶ Y) (qW : PY ⟶ W)
    (u' : U ⟶ PX) (v' : V ⟶ PY)
    (sqX : IsPullback pX.hom pW.hom fX.hom c.hom)
    (sqY : IsPullback qY.hom qW.hom gY.hom c.hom)
    (hu'X : u' ≫ pX = a) (hu'W : u' ≫ pW = uw)
    (hv'Y : v' ≫ qY = b) (hv'W : v' ≫ qW = vw)
    (hcEtale : IsEtale B S hS c.hom) (hcSurj : IsSurjective B S hS c.hom)
    (haEtale : IsEtale B S hS a.hom) (hbEtale : IsEtale B S hS b.hom)
    (huEtale : IsEtale B S hS u'.hom) (huSurj : IsSurjective B S hS u'.hom)
    (hvEtale : IsEtale B S hS v'.hom) (hvSurj : IsSurjective B S hS v'.hom)
    (h : TorIndependent U.2 V.2 W.2 uw.hom vw.hom) :
    TorIndependent X.2 Y.2 Bs.2 fX.hom gY.hom := by
  intro x y hxy
  obtain ⟨w₀, hw₀⟩ := hcSurj (geometricPointMap fX.hom x).image
  obtain ⟨wbar, -, hwbar⟩ := exists_geometricPoint_lift_of_isEtale B S hS W.2 Bs.2 c.hom
    hcEtale (geometricPointMap fX.hom x) w₀ hw₀
  have hcw : geometricPointMap c.hom wbar = geometricPointMap fX.hom x := Subtype.ext hwbar
  obtain ⟨px, hpx1, hpx2⟩ := exists_geometricPoint_of_isPullback B S hS sqX x wbar hcw.symm
  obtain ⟨u₀, hu₀⟩ := huSurj px.image
  obtain ⟨ubar, -, hubar⟩ := exists_geometricPoint_lift_of_isEtale B S hS U.2 PX.2 u'.hom
    huEtale px u₀ hu₀
  have hu : geometricPointMap u'.hom ubar = px := Subtype.ext hubar
  obtain ⟨py, hpy1, hpy2⟩ :=
    exists_geometricPoint_of_isPullback B S hS sqY y wbar (hcw.trans hxy).symm
  obtain ⟨v₀, hv₀⟩ := hvSurj py.image
  obtain ⟨vbar, -, hvbar⟩ := exists_geometricPoint_lift_of_isEtale B S hS V.2 PY.2 v'.hom
    hvEtale py v₀ hv₀
  have hv : geometricPointMap v'.hom vbar = py := Subtype.ext hvbar
  have hpt : ∀ {P Q R : AlgebraicSpaces B S hS} (m : P ⟶ Q) (n : Q ⟶ R) (k : P ⟶ R)
      (p : GeometricPoint B S hS P.1) (q : GeometricPoint B S hS Q.1)
      (r : GeometricPoint B S hS R.1), m ≫ n = k → geometricPointMap m.hom p = q →
      geometricPointMap n.hom q = r → geometricPointMap k.hom p = r := by
    rintro _ _ _ m n _ p _ _ rfl rfl rfl
    rfl
  have hsq : ∀ {P Q R T Z : AlgebraicSpaces B S hS} (m : P ⟶ Q) (n₁ : Q ⟶ R) (n₂ : Q ⟶ T)
      (f : R ⟶ Z) (g : T ⟶ Z) (k₁ : P ⟶ R) (k₂ : P ⟶ T), m ≫ n₁ = k₁ → m ≫ n₂ = k₂ →
      n₁.hom ≫ f.hom = n₂.hom ≫ g.hom → k₂.hom ≫ g.hom = k₁.hom ≫ f.hom := by
    rintro _ _ _ _ _ m n₁ n₂ f g _ _ rfl rfl sq
    change (m.hom ≫ n₂.hom) ≫ g.hom = (m.hom ≫ n₁.hom) ≫ f.hom
    rw [Category.assoc, Category.assoc, sq]
  have hax := hpt u' pX a ubar px x hu'X hu hpx1
  have huw := hpt u' pW uw ubar px wbar hu'W hu hpx2
  have hby := hpt v' qY b vbar py y hv'Y hv hpy1
  have hvw := hpt v' qW vw vbar py wbar hv'W hv hpy2
  have hsqU := hsq u' pX pW fX c a uw hu'X hu'W sqX.w
  have hsqV := hsq v' qY qW gY c b vw hv'Y hv'W sqY.w
  subst hax
  subst hby
  subst huw
  obtain ⟨phiU, psiV, hphiU, hpsiV, hTor⟩ := h ubar vbar hvw.symm
  have hmUW := eq_etaleLocalRingMap U.2 uw.hom ubar hphiU
  have hmVW := eq_etaleLocalRingMap V.2 vw.hom vbar hpsiV
  have hmA := eq_etaleLocalRingMap U.2 a.hom ubar
    (isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv B S hS a haEtale ubar)
  have hmB := eq_etaleLocalRingMap V.2 b.hom vbar
    (isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv B S hS b hbEtale vbar)
  have hmCU := eq_etaleLocalRingMap W.2 c.hom (geometricPointMap uw.hom ubar)
    (isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv B S hS c hcEtale _)
  have hmCV := eq_etaleLocalRingMap W.2 c.hom (geometricPointMap vw.hom vbar)
    (isEtaleLocalRingMap_etaleLocalRingIsoOfIsEtale_inv B S hS c hcEtale _)
  have keyU := etaleLocalRingMap_comp_eq B S hS uw c a fX hsqU ubar hcw.symm
  have keyV := etaleLocalRingMap_comp_eq B S hS vw c b gY hsqV vbar
    ((congrArg (geometricPointMap c.hom) hvw).trans (hcw.trans hxy)).symm
  refine ⟨etaleLocalRingMap X.2 fX.hom (geometricPointMap a.hom ubar),
    etaleLocalRingMap Y.2 gY.hom (geometricPointMap b.hom vbar),
    etaleLocalRingMap_isEtaleLocalRingMap X.2 fX.hom _,
    etaleLocalRingMap_isEtaleLocalRingMap Y.2 gY.hom _, ?_⟩
  refine torIndependent_of_ringEquiv _ _ _ _
    (etaleLocalRingIsoOfIsEtale B S hS c hcEtale (geometricPointMap uw.hom ubar) ≪≫
      eqToIso (congrArg (etaleLocalRing B S hS Bs.1) hcw)).commRingCatIsoToRingEquiv
    (etaleLocalRingIsoOfIsEtale B S hS a haEtale ubar).commRingCatIsoToRingEquiv
    (etaleLocalRingIsoOfIsEtale B S hS b hbEtale vbar).commRingCatIsoToRingEquiv
    ?_ ?_ hTor
  · intro r
    have hcancel : ((etaleLocalRingMap W.2 c.hom (geometricPointMap uw.hom ubar)).comp
          (eqToHom (congrArg (etaleLocalRing B S hS Bs.1) hcw.symm)).hom).comp
          ((etaleLocalRingIsoOfIsEtale B S hS c hcEtale (geometricPointMap uw.hom ubar) ≪≫
            eqToIso (congrArg (etaleLocalRing B S hS Bs.1) hcw)).hom.hom) =
        RingHom.id _ := by
      rw [← hmCU]
      ext t
      simp only [RingHom.comp_apply, RingHom.id_apply, Iso.trans_hom, CommRingCat.hom_comp,
        eqToIso.hom]
      rw [eqToHom_hom_eqToHom_hom]
      exact iso_inv_hom_hom_hom
        (etaleLocalRingIsoOfIsEtale B S hS c hcEtale (geometricPointMap uw.hom ubar)) t
    have ht := DFunLike.congr_fun keyU
      ((etaleLocalRingIsoOfIsEtale B S hS c hcEtale (geometricPointMap uw.hom ubar) ≪≫
        eqToIso (congrArg (etaleLocalRing B S hS Bs.1) hcw)).hom.hom r)
    have hc0 := DFunLike.congr_fun hcancel r
    simp only [RingHom.comp_apply, RingHom.id_apply] at ht hc0
    rw [hc0, ← hmUW, ← hmA] at ht
    rw [ht]
    exact iso_hom_hom_inv_hom (etaleLocalRingIsoOfIsEtale B S hS a haEtale ubar) _
  · intro r
    have hcongr := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (etaleLocalRingIsoOfIsEtale_congr B S hS c hcEtale hvw.symm)) r
    have ht := DFunLike.congr_fun keyV
      ((eqToHom (congrArg (etaleLocalRing B S hS Bs.1) hxy)).hom
        ((etaleLocalRingIsoOfIsEtale B S hS c hcEtale (geometricPointMap uw.hom ubar) ≪≫
          eqToIso (congrArg (etaleLocalRing B S hS Bs.1) hcw)).hom.hom r))
    simp only [RingHom.comp_apply, Iso.trans_hom, CommRingCat.hom_comp, eqToIso.hom,
      CommRingCat.hom_ofHom] at ht hcongr ⊢
    rw [eqToHom_hom_trans₃ _ _ _ (congrArg (etaleLocalRing B S hS Bs.1)
      (congrArg (geometricPointMap c.hom) hvw.symm)), ← hmCV, ← hcongr,
      iso_inv_hom_hom_hom, ← hmVW, ← hmB] at ht
    rw [ht]
    exact iso_hom_hom_inv_hom (etaleLocalRingIsoOfIsEtale B S hS b hbEtale vbar) _

/-! ### Stacks 08IQ, condition (1) implies condition (3) -/

/-- **Stacks 08IQ, (1) ⟹ (3).**  Let `X` and `Y` be algebraic spaces over an algebraic space
`Bs` which are Tor independent over `Bs`.  Then there is a commutative diagram
```
U ⟶ W ⟵ V
↓    ↓    ↓
X ⟶ Bs ⟵ Y
```
with étale vertical arrows in which `W ⟶ Bs` is surjective, in which `U` and `V` are étale and
surjective over the fibre products `X ×_{Bs} W` and `Y ×_{Bs} W`, and in which `U` and `V` are
Tor independent over `W`: this is the existence asserted by condition (3).

The witness is the diagram of identities, `W = Bs`, `U = X` and `V = Y`, whose two fibre
products are `X` and `Y` themselves by `CategoryTheory.IsPullback.of_id_fst`; the Tor
independence asked of the diagram is then the hypothesis on the nose.  The converse implication
is `AlgebraicGeometry.Space.torIndependent_of_isEtale_surjective_diagram`. -/
@[stacks 08IQ "(1) => (3)"]
public theorem exists_isEtale_surjective_diagram_of_torIndependent
    {Bs X Y : AlgebraicSpaces B S hS} (fX : X ⟶ Bs) (gY : Y ⟶ Bs)
    (h : TorIndependent X.2 Y.2 Bs.2 fX.hom gY.hom) :
    ∃ (U V W PX PY : AlgebraicSpaces B S hS) (c : W ⟶ Bs) (a : U ⟶ X) (uw : U ⟶ W)
      (b : V ⟶ Y) (vw : V ⟶ W) (pX : PX ⟶ X) (pW : PX ⟶ W) (qY : PY ⟶ Y) (qW : PY ⟶ W)
      (u' : U ⟶ PX) (v' : V ⟶ PY),
      IsPullback pX.hom pW.hom fX.hom c.hom ∧ IsPullback qY.hom qW.hom gY.hom c.hom ∧
        u' ≫ pX = a ∧ u' ≫ pW = uw ∧ v' ≫ qY = b ∧ v' ≫ qW = vw ∧
        IsEtale B S hS c.hom ∧ IsSurjective B S hS c.hom ∧
        IsEtale B S hS a.hom ∧ IsEtale B S hS b.hom ∧
        IsEtale B S hS u'.hom ∧ IsSurjective B S hS u'.hom ∧
        IsEtale B S hS v'.hom ∧ IsSurjective B S hS v'.hom ∧
        TorIndependent U.2 V.2 W.2 uw.hom vw.hom := by
  have hsurj : ∀ (F : AlgebraicSpaces B S hS), IsSurjective B S hS (𝟙 F.1) :=
    fun F z => ⟨z, congrFun (pointsMap_id B S hS F.1) z⟩
  exact ⟨X, Y, Bs, X, Y, 𝟙 Bs, 𝟙 X, fX, 𝟙 Y, gY, 𝟙 X, fX, 𝟙 Y, gY, 𝟙 X, 𝟙 Y,
    IsPullback.of_id_fst, IsPullback.of_id_fst, Category.id_comp _, Category.id_comp _,
    Category.id_comp _, Category.id_comp _, isEtale_of_isIso B S hS (𝟙 Bs.1), hsurj Bs,
    isEtale_of_isIso B S hS (𝟙 X.1), isEtale_of_isIso B S hS (𝟙 Y.1),
    isEtale_of_isIso B S hS (𝟙 X.1), hsurj X, isEtale_of_isIso B S hS (𝟙 Y.1), hsurj Y, h⟩

end AlgebraicGeometry.Space

end
